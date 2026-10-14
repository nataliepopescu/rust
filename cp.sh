#!/usr/bin/env bash
# Copies every rustc_* .rmeta file (crate metadata, needed at compile time)
# and every .so file (needed at link/run time, including proc-macro crates'
# own .so - see below) from a stage's own "-rustc" build directories into
# that same stage's sysroot - what an external, rustc_private-based tool
# (like verifopt's monomorph) actually links against.
#
# Needed because bootstrap deliberately does *not* copy these by default
# (see compile.rs's own "we intentionally don't copy `rustc-dev` artifacts
# until they're requested with `builder.ensure(Rustc)`" - the mechanism
# to trigger that automatically wasn't pinned down this session), and
# because the sysroot gets wiped on every `./x.py` invocation regardless -
# so this has to be re-run after every rebuild of the compiler itself.
#
# There are actually *two* separate build-output directories per stage, not
# one - confirmed empirically, not assumed:
#   stage<N>-rustc/release/deps/                 - host-side artifacts
#                                                   (proc-macro crates like
#                                                   rustc_macros, and their
#                                                   own dependencies like
#                                                   derive_where, which run
#                                                   *during* compilation
#                                                   rather than getting
#                                                   linked into rustc itself)
#   stage<N>-rustc/<host-triple>/release/deps/    - target-side artifacts
#                                                   (rustc_middle and
#                                                   friends, which actually
#                                                   get linked into the
#                                                   final rustc binary)
# Both need their .rmeta copied - rustc's own metadata validation walks the
# whole dependency graph, including crates whose actual code never gets
# re-run, so their metadata still has to be resolvable even though only
# their already-compiled effects (not the crates themselves) matter here.
#
# Usage: copy_rustc_private_artifacts.sh [stage] [host-triple]
#   stage        defaults to 2 (matches the version-tagging fix - stage1's
#                own -rustc metadata is tagged by stage0, a different
#                compiler version than stage1 itself, which is what broke
#                things; stage2's own -rustc metadata is tagged by stage1,
#                matching stage2's own version)
#   host-triple  defaults to x86_64-unknown-linux-gnu

set -euo pipefail

STAGE="${1:-2}"
HOST="${2:-x86_64-unknown-linux-gnu}"

RUST_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# If this script isn't placed at the rust repo's own root, override via:
#   RUST_ROOT=~/hack/rust ./copy_rustc_private_artifacts.sh
if [ ! -d "$RUST_ROOT/build" ]; then
    echo "error: no 'build' directory found at $RUST_ROOT - if this script" >&2
    echo "       isn't sitting at your rust repo's own root, set RUST_ROOT" >&2
    echo "       explicitly, e.g.: RUST_ROOT=~/hack/rust $0 $*" >&2
    exit 1
fi

STAGE_RUSTC_ROOT="$RUST_ROOT/build/$HOST/stage${STAGE}-rustc"
SRC_HOST="$STAGE_RUSTC_ROOT/release/deps"
SRC_TARGET="$STAGE_RUSTC_ROOT/$HOST/release/deps"
SYSROOT_LIB="$RUST_ROOT/build/$HOST/stage${STAGE}/lib/rustlib/$HOST/lib"
STAGE_RUSTC="$RUST_ROOT/build/$HOST/stage${STAGE}/bin/rustc"

if [ ! -d "$SRC_HOST" ] && [ ! -d "$SRC_TARGET" ]; then
    echo "error: neither $SRC_HOST nor $SRC_TARGET exists - has stage $STAGE" >&2
    echo "       actually been built? (./x.py build --stage $STAGE)" >&2
    exit 1
fi

if [ ! -x "$STAGE_RUSTC" ]; then
    echo "error: $STAGE_RUSTC not found or not executable" >&2
    exit 1
fi

mkdir -p "$SYSROOT_LIB"

# Copy every .rmeta AND every .so from both directories - not just
# librustc_driver-*.so. Proc-macro crates (rustc_macros, and their own
# dependencies like derive_where) confirmed - directly, against the real,
# official `rustc-dev` dist tarball, not just this build - to produce NO
# .rmeta at all, ever, even in the "correct" mechanism. They still need
# their own .so present, though, since they get loaded dynamically at
# compile time (to actually run their macro-expansion code) rather than
# being statically linked into rustc_driver.so the way ordinary library
# crates are. Copying every .so (not just one, specifically-matched one)
# is what actually covers this - extra, unused .so files sitting in the
# sysroot are harmless, since rustc's own crate-loader picks the specific
# hash a referencing crate's metadata actually names, not just whichever
# file happens to exist.
total_rmeta=0
total_so=0
for src in "$SRC_HOST" "$SRC_TARGET"; do
    if [ -d "$src" ]; then
        rcount="$(find "$src" -maxdepth 1 -name '*.rmeta' | wc -l)"
        scount="$(find "$src" -maxdepth 1 -name '*.so' | wc -l)"
        echo "Copying from $src ($rcount .rmeta, $scount .so) ..."
        cp "$src"/*.rmeta "$SYSROOT_LIB"/ 2>/dev/null || true
        cp "$src"/*.so "$SYSROOT_LIB"/ 2>/dev/null || true
        total_rmeta=$((total_rmeta + rcount))
        total_so=$((total_so + scount))
    else
        echo "  (skipping $src - does not exist)"
    fi
done
echo "  done ($total_rmeta .rmeta, $total_so .so total)"

# Keep only the *current* build of each rustc_* crate in the sysroot.
#
# Cargo never deletes old artifacts from deps/, so whenever a change alters
# the compiler's crate graph (adding a dependency to a rustc_* crate, a new
# compiler crate, ...), the affected crates get new hashes and the old ones
# stay behind - and the blanket copy above puts them back into the sysroot.
# That's harmless for crates found *through* other crates' metadata (which
# names the exact hash), but not for crates loaded *by name*: a
# rustc_private tool's `extern crate rustc_driver;` then fails with
# "multiple candidates for dylib dependency rustc_driver" (E0464).
#
# Only the compiler's own workspace crates are pruned - those with a
# directory under compiler/ (rustc_driver, rustc_middle, ...): a build has
# exactly one of each, so any other hash is stale. Everything else is left
# alone, whatever its name: third-party crates can legitimately exist in
# several versions at once (resolved by hash) - including some named rustc_*,
# like rustc_hash (the crates.io rustc-hash crate) - and the standard
# library's own dependencies (e.g. its libc) must never be touched, since
# std's metadata names their exact hash. "Current" = newest modification time in the build
# directory (actual build time; mtimes in the sysroot are just copy times).
echo
echo "Pruning stale rustc_* builds from the sysroot ..."
pruned=0
# (find rather than ls, and `|| true`: under `set -euo pipefail` a glob that
# matches nothing - e.g. no .rlib files - would otherwise abort the script.)
for crate in $( (find "$SYSROOT_LIB" -maxdepth 1 -name 'librustc_*-*' \
                   \( -name '*.rmeta' -o -name '*.rlib' -o -name '*.so' \) -printf '%f\n' || true) \
                 | sed -E 's/-[0-9a-f]{16}\.(rlib|rmeta|so)$//' | sort -u); do
    # A compiler workspace crate? (librustc_driver -> compiler/rustc_driver)
    [ -d "$RUST_ROOT/compiler/${crate#lib}" ] || continue
    hashes="$( (find "$SYSROOT_LIB" -maxdepth 1 -name "$crate-*" -printf '%f\n' || true) \
               | grep -E "^$crate-[0-9a-f]{16}\." | sed -E 's/.*-([0-9a-f]{16})\..*/\1/' | sort -u || true)"
    [ -n "$hashes" ] || continue
    [ "$(echo "$hashes" | wc -l)" -gt 1 ] || continue
    newest="$( (ls -t "$SRC_HOST/$crate"-*.rmeta "$SRC_HOST/$crate"-*.so \
                     "$SRC_TARGET/$crate"-*.rmeta "$SRC_TARGET/$crate"-*.so 2>/dev/null || true) \
               | grep -E "/$crate-[0-9a-f]{16}\." | head -1 | sed -E 's/.*-([0-9a-f]{16})\..*/\1/' || true)"
    if [ -z "$newest" ]; then
        echo "  WARNING: $crate has several builds in the sysroot but none in the build dirs - left as is" >&2
        continue
    fi
    for h in $hashes; do
        if [ "$h" != "$newest" ]; then
            rm -f "$SYSROOT_LIB/$crate-$h".*
            echo "  removed $crate-$h (kept $newest)"
            pruned=$((pruned + 1))
        fi
    done
done
echo "  done ($pruned stale build(s) removed)"

echo
echo "Done. Sysroot populated at: $SYSROOT_LIB"
echo "(re-run this script after any ./x.py build/check invocation, since" \
     "that wipes the sysroot and takes this copy with it)"
