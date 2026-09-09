#!/usr/bin/env bash
# Copies the rustc_* .rmeta files (crate metadata, needed at compile time)
# and the matching .so files (needed at compile/link/run time, e.g.
# proc-macro crates like rustc_macros/derive_where, and librustc_driver
# itself) from a stage's own "-rustc" build directories into that same
# stage's sysroot - what an external, rustc_private-based tool (like
# verifopt's monomorph) actually links against.
#
# Needed because bootstrap deliberately does *not* copy these by default
# (see compile.rs's own "we intentionally don't copy `rustc-dev` artifacts
# until they're requested with `builder.ensure(Rustc)`" - the mechanism
# to trigger that automatically wasn't pinned down this session), and
# because the sysroot gets wiped on every `./x.py` invocation regardless -
# so this has to be re-run after every rebuild of the compiler itself.
#
# There are two separate source directories, and both matter:
#   - stage${STAGE}-rustc/release/deps           (host-side: proc-macro
#     crates like rustc_macros, derive_where - these have no separate
#     target-triple build at all, since they run on the host at compile
#     time, and only ever produce a .so, never a .rmeta)
#   - stage${STAGE}-rustc/$HOST/release/deps     (target-side: rustc_middle,
#     rustc_hir, librustc_driver, and most everything else)
# Copying from only one of these produces "can't find crate" errors for
# whichever crates only live in the other one.
#
# THE KEY DISTINCTION, learned the hard way across two earlier, wrong
# versions of this script:
#   - Some crates in stage${STAGE}-rustc's own deps directory (e.g. libc)
#     are *also* ordinary dependencies that std itself was built against,
#     by the normal ./x.py build - correctly placed in the sysroot
#     already. These must NEVER be touched: overwriting one with a
#     different build of the same crate from rustc's own, separate cargo
#     build breaks std's own ability to load at all (rustc's own error:
#     "found possibly newer version of crate `libc` which `std` depends
#     on", cascading into "cannot resolve a prelude import" and "can't
#     find crate for `std`" absolutely everywhere downstream).
#   - Other crates (e.g. smallvec, anstyle, and most of the rustc_*
#     crates themselves) are *only* ever dependencies of the compiler
#     crates - bootstrap never places these in the sysroot at all. If
#     one is already present, it can only have gotten there via an
#     *earlier run of this very script*, against a since-superseded
#     rustc build - and must be refreshed, not preserved, or a rebuilt
#     rustc_data_structures/rustc_interface/etc. ends up paired with a
#     stale copy of something it depends on (rustc's own error: "found
#     possibly newer version of crate `smallvec` which
#     `rustc_data_structures` depends on").
#
# Blanket "always overwrite" breaks the first kind (libc); blanket "never
# overwrite what's already there" breaks the second kind (smallvec) - both
# were tried, in that order, and both were wrong. The distinguishing
# signal: libstd's own mtime, in the sysroot, as an anchor. Right after a
# fresh ./x.py build, before this script has ever touched anything, every
# normally-placed file (libstd itself included) shares roughly the same,
# early mtime. Anything this script copies in is necessarily newer than
# that, since it happens after the ./x.py build completes. So: an
# existing sysroot file older than or equal to libstd's own mtime was
# placed by the normal build (never touch it); one newer than that was
# placed by this script on an earlier run (safe to refresh).
#
# Deduplication also applies *within* each source directory itself:
# cargo's own "deps" directory is well known to accumulate multiple,
# differently-hashed builds of the same crate across rebuilds without
# cleaning old ones out on its own, so for each crate-name prefix (a
# file's own name minus its trailing "-<hash>.ext"), only the newest (by
# mtime) file found in the source directory is considered for copying.
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

HOST_SRC="$RUST_ROOT/build/$HOST/stage${STAGE}-rustc/release/deps"
TARGET_SRC="$RUST_ROOT/build/$HOST/stage${STAGE}-rustc/$HOST/release/deps"
SYSROOT_LIB="$RUST_ROOT/build/$HOST/stage${STAGE}/lib/rustlib/$HOST/lib"
STAGE_RUSTC="$RUST_ROOT/build/$HOST/stage${STAGE}/bin/rustc"

if [ ! -d "$TARGET_SRC" ]; then
    echo "error: $TARGET_SRC does not exist - has stage $STAGE actually been built?" >&2
    echo "       (./x.py build --stage $STAGE)" >&2
    exit 1
fi

if [ ! -x "$STAGE_RUSTC" ]; then
    echo "error: $STAGE_RUSTC not found or not executable" >&2
    exit 1
fi

mkdir -p "$SYSROOT_LIB"

LIBSTD_GLOB=("$SYSROOT_LIB"/libstd-*.rlib)
if [ ! -e "${LIBSTD_GLOB[0]}" ]; then
    echo "error: no libstd-*.rlib found in $SYSROOT_LIB - this script uses" >&2
    echo "       its own mtime as an anchor to tell normally-placed sysroot" >&2
    echo "       files apart from ones it previously copied itself, and" >&2
    echo "       can't do that without it. Has stage $STAGE actually been" >&2
    echo "       built? (./x.py build --stage $STAGE)" >&2
    exit 1
fi
ANCHOR_MTIME="$(stat -c %Y "${LIBSTD_GLOB[0]}" 2>/dev/null || stat -f %m "${LIBSTD_GLOB[0]}")"

# For each file matching a glob pattern in $1: finds the newest (by
# mtime) file under each crate-name prefix within the source directory
# itself, then either copies it in (nothing with that prefix exists in
# SYSROOT_LIB yet), refreshes it (something with that prefix exists, but
# it's newer than ANCHOR_MTIME, meaning this script itself placed it on
# an earlier run), or leaves it alone (something with that prefix
# exists, at or older than ANCHOR_MTIME, meaning the normal ./x.py build
# placed it - never touched, regardless of what's in the source
# directory). Prints how many files were copied/refreshed and how many
# were left alone as normally-placed.
copy_or_refresh() {
    local src_dir="$1" pattern="$2"
    local -A newest_path=() newest_mtime=()
    local f base prefix mtime copied=0 kept=0
    local existing existing_mtime

    shopt -s nullglob
    for f in "$src_dir"/$pattern; do
        base="$(basename "$f")"
        prefix="${base%-*}"
        mtime="$(stat -c %Y "$f" 2>/dev/null || stat -f %m "$f")"
        if [ -z "${newest_mtime[$prefix]:-}" ] || [ "$mtime" -gt "${newest_mtime[$prefix]}" ]; then
            newest_mtime[$prefix]="$mtime"
            newest_path[$prefix]="$f"
        fi
    done
    shopt -u nullglob

    for prefix in "${!newest_path[@]}"; do
        existing=""
        for cand in "$SYSROOT_LIB/${prefix}"-*; do
            [ -e "$cand" ] && existing="$cand" && break
        done
        if [ -n "$existing" ]; then
            existing_mtime="$(stat -c %Y "$existing" 2>/dev/null || stat -f %m "$existing")"
            if [ "$existing_mtime" -le "$ANCHOR_MTIME" ]; then
                kept=$((kept + 1))
                continue
            fi
            rm -f "$SYSROOT_LIB/${prefix}"-*
        fi
        cp "${newest_path[$prefix]}" "$SYSROOT_LIB"/
        copied=$((copied + 1))
    done
    echo "$copied $kept"
}

for src_dir in "$HOST_SRC" "$TARGET_SRC"; do
    [ -d "$src_dir" ] || continue
    for pattern in '*.rmeta' '*.so'; do
        echo "Scanning $pattern files in $src_dir ..."
        read -r n_copied n_kept <<< "$(copy_or_refresh "$src_dir" "$pattern")"
        echo "  copied/refreshed $n_copied, left $n_kept normally-placed file(s) alone"
    done
done

# Sanity check, not the primary copy mechanism: confirm the exact
# librustc_driver-*.so this stage's own rustc binary actually loads at
# runtime is present in the sysroot at all.
DRIVER_SO_LINE="$(ldd "$STAGE_RUSTC" | grep 'librustc_driver' || true)"
if [ -n "$DRIVER_SO_LINE" ]; then
    DRIVER_SO_NAME="$(echo "$DRIVER_SO_LINE" | awk '{print $1}')"
    if [ ! -f "$SYSROOT_LIB/$DRIVER_SO_NAME" ]; then
        echo "warning: ldd reports $STAGE_RUSTC depends on $DRIVER_SO_NAME," >&2
        echo "         but that exact file isn't present in $SYSROOT_LIB -" >&2
        echo "         check whether a different-hashed librustc_driver got" >&2
        echo "         copied there instead" >&2
    fi
fi

echo
echo "Done. Sysroot populated at: $SYSROOT_LIB"
echo "(re-run this script after any ./x.py build/check invocation, since" \
     "that wipes the sysroot and takes this copy with it)"
