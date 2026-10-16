use rustc_data_structures::fx::{FxHashSet as HashSet};

use rustc_data_structures::smallvec::SmallVec;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, CastKind, CoercionSource, Const, ConstOperand, Local,
    LocalDecl, Mutability, Operand, Place, ProjectionElem, Rvalue, SourceInfo, Statement,
    StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp,
};
use rustc_middle::mir::{InlineAsmOperand, START_BLOCK};
use rustc_span::def_id::{DefPathHash, LOCAL_CRATE};
use rustc_hir::LangItem;
use rustc_hir::attrs::Linkage;
use rustc_hir::Safety;
use rustc_hir::def::DefKind;
use rustc_middle::mir::pretty::MirWriter;
use rustc_middle::ty;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{
    AssocKind, FnDef, GenericArg, Instance, InstanceKind, List, Ty, TyCtxt, TypingEnv, VtblEntry,
};
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::mir::mono::{CodegenUnit, MonoItem};
use rustc_span::def_id::DefId;
use rustc_span::Span;

use std::fs::{File, OpenOptions};
use std::io::Write;

//use std::collections::{HashMap, HashSet};
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use tracing::{debug, trace};

use rustc_verifopt::{ShapeRegistry, Store, arg_from_hash, def_id_from_hash, hash_args};


pub(super) fn dep_rewrite_store_path() -> std::path::PathBuf {
    verifopt_out_dir().join("verifopt_store.json")
}

static SHARED_STORE: OnceLock<Option<Store>> = OnceLock::new();

fn load_shared_store() -> Option<Store> {
    let contents = match std::fs::read_to_string(dep_rewrite_store_path()) {
        Ok(c) => c,
        Err(e) => {
            debug!(
                "[verifopt debug] could not read {}: {e}",
                dep_rewrite_store_path().display()
            );
            return None;
        }
    };
    debug!(
        "[verifopt debug] read {} bytes from {}",
        contents.len(),
        dep_rewrite_store_path().display()
    );
    let store = match Store::from_json(&contents) {
        Ok(s) => s,
        Err(e) => {
            debug!(
                "[verifopt debug] failed to deserialize {}: {e}",
                dep_rewrite_store_path().display()
            );
            return None;
        }
    };
    debug!(
        "[verifopt debug] loaded store: {} target entries, {} tag entries, {} shape entries",
        store.targets.len(),
        store.tags.len(),
        store.shapes.len()
    );
    // Seed the shape registry from the store's own shapes, read off disk -
    // this is what lets arg_from_hash (see fn_op) resolve a sentinel hash
    // this process never independently computed itself.
    SHAPES.seed(&store.shapes);
    Some(store)
}


static DYNAMIC_HITS: AtomicUsize = AtomicUsize::new(0);

static FN_OP_ARGS_MISMATCH: AtomicUsize = AtomicUsize::new(0);
static FN_OP_ARGS_OK: AtomicUsize = AtomicUsize::new(0);

static CRATE_NAME: OnceLock<String> = OnceLock::new();

/// Where every per-build output file goes: `VERIFOPT_STORE_DIR` (which
/// cargo-verifopt sets on every rustc it spawns, dependencies included), else
/// this process's CWD - the same resolution as dep_rewrite_store_path.
/// Previously these used plain relative paths, so each crate's output landed
/// in whatever CWD cargo gave its rustc (e.g. a crates.io dependency's own
/// directory under ~/.cargo/registry/src), scattered across the filesystem.
///
/// cargo-verifopt points VERIFOPT_STORE_DIR at `<run dir>/verifopt_results`,
/// the one directory for all of a run's verifopt outputs. Without it (a
/// hand-run rustc), fall back to `./verifopt_results`, matching the plugin's
/// rewrite::results_dir.
fn verifopt_out_dir() -> std::path::PathBuf {
    match std::env::var_os("VERIFOPT_STORE_DIR") {
        Some(dir) => std::path::PathBuf::from(dir),
        None => std::path::PathBuf::from("verifopt_results"),
    }
}

/// Directory of per-crate MIR dumps: one file per rustc process, named
/// `<crate>-<stable crate id>.txt`. One file per process (rather than one
/// shared mir_dump.txt) because cargo compiles crates in parallel: appends
/// from different processes would interleave in a shared file, and land in
/// whatever order the processes happened to finish. Separate files never
/// interleave, and reading them in sorted file-name order is deterministic.
/// The stable crate id tells apart different compilations of a same-named
/// crate (e.g. `rg` the binary vs `rg` the test harness).
const MIR_DUMP_DIR: &str = "verifopt_mir_dumps";

static MIR_DUMP_FILE: OnceLock<Mutex<File>> = OnceLock::new();

fn mir_dump_file(tcx: TyCtxt<'_>) -> &'static Mutex<File> {
    MIR_DUMP_FILE.get_or_init(|| {
        let dir = verifopt_out_dir().join(MIR_DUMP_DIR);
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join(format!(
            "{}-{:016x}.txt",
            tcx.crate_name(LOCAL_CRATE),
            tcx.stable_crate_id(LOCAL_CRATE).as_u64()
        ));
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap_or_else(|e| panic!("failed to open {} for writing: {e}", path.display()));
        Mutex::new(file)
    })
}

static EDIT_KIND_STATS_FILE: OnceLock<Mutex<File>> = OnceLock::new();

/// One shared file for the whole build (lines are only ever counted, so
/// cross-process order doesn't matter); each line is appended with a single
/// write, so lines from parallel rustc processes can't interleave.
fn edit_kind_stats_file() -> &'static Mutex<File> {
    EDIT_KIND_STATS_FILE.get_or_init(|| {
        let dir = verifopt_out_dir();
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("verifopt_edit_kind_stats.txt");
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap_or_else(|e| panic!("failed to open {} for writing: {e}", path.display()));
        Mutex::new(file)
    })
}

/// Appends one line recording a single, successfully-applied rewrite's
/// own kind - called only at the point within each of apply_edits' own
/// three match arms (Single/Pointers/Tagged) where the rewrite has
/// actually, genuinely gone through, past every earlier continue-style
/// bail-out for an unsupported or mismatched case - so this counts
/// applied rewrites, not merely attempted ones. Appends (like
/// mir_dump_file above) rather than overwrites, since apply_edits is
/// called once per rewritten function within a single rustc invocation,
/// and a full build spans several, separate invocations (one per
/// crate) - appending is what lets counts naturally accumulate across
/// both, without needing any kind of end-of-process hook at all (which
/// `static` values in Rust don't get: their own Drop, if any, never
/// runs at process exit).
fn log_edit_kind(kind: &str) {
    let mut file = edit_kind_stats_file().lock().unwrap();
    let _ = file.write_all(format!("{kind}\n").as_bytes());
}

fn dump_body<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>, body: &Body<'tcx>, label: &str) {
    let mut buf = Vec::new();

    let writer = MirWriter::new(tcx);
    let _ = ty::print::with_no_trimmed_paths!(writer.write_mir_fn(body, &mut buf));

    // Where this rewrite applied. The `fn` line MirWriter prints uses the
    // function's short name, so e.g. a `fmt` in the top-level crate and one
    // in a dependency were indistinguishable in a combined dump. Cargo sets
    // CARGO_PKG_NAME/CARGO_PKG_VERSION for every rustc it runs (dependencies
    // included); outside cargo, fall back to the crate name alone. The
    // instance line adds the generic args, which tell apart different
    // monomorphizations of one generic function (possibly in several crates).
    // The `######### MIR ... #########` line itself is unchanged, since
    // tools (split_mir.py) split on it.
    let krate = tcx.crate_name(LOCAL_CRATE);
    let package = match (std::env::var("CARGO_PKG_NAME"), std::env::var("CARGO_PKG_VERSION")) {
        (Ok(name), Ok(version)) => format!(" (package {name} {version})"),
        _ => String::new(),
    };
    let def_path = ty::print::with_no_trimmed_paths!(tcx.def_path_str(instance.def_id()));
    let instance_str = ty::print::with_no_trimmed_paths!(instance.to_string());

    // Assembled first and appended with one write, so a dump is never split.
    let mut out = format!(
        "\n######### MIR {label} #########\n\
         // crate: {krate}{package}\n\
         // fn: {def_path}\n\
         // instance: {instance_str}\n"
    )
    .into_bytes();
    out.extend_from_slice(&buf);
    out.extend_from_slice(format!("######### END {label} #########\n\n").as_bytes());
    let mut file = mir_dump_file(tcx).lock().unwrap();
    let _ = file.write_all(&out);
}

enum Edit {
    Single(DefPathHash, Option<Vec<DefPathHash>>),
    /// A provably single target given as an exact instance (Store::exact):
    /// the function and its own generic args.
    SingleExact(DefPathHash, Vec<DefPathHash>),
    Pointers(Vec<(DefPathHash, Option<Vec<DefPathHash>>)>),
    Tagged(Vec<(usize, usize, u64, DefPathHash, Option<Vec<DefPathHash>>)>),
}

/// Up to how many candidates a Pointers rewrite compares the vtable slot
/// against (a site with more targets isn't rewritten; a longer expanded list
/// is cut to this - any subset is sound). Default 4; override with the
/// VERIFOPT_MAX_CANDIDATES environment variable, which `cargo verifopt
/// --max-candidates N` sets for every rustc it starts.
fn max_pointers_candidates() -> usize {
    static MAX: OnceLock<usize> = OnceLock::new();
    *MAX.get_or_init(|| {
        std::env::var("VERIFOPT_MAX_CANDIDATES")
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
            .filter(|n| *n >= 1)
            .unwrap_or(4)
    })
}

/// Sentinel hash -> shape, for every type this process hashed itself or read
/// from the store (see load_shared_store). The hashing scheme itself lives in
/// rustc_verifopt, shared with the analysis plugin.
static SHAPES: ShapeRegistry = ShapeRegistry::new();

// The store.targets.keys()/store.tags.keys() check below is order-
// independent (just checks whether any entry matches at all), so
// HashMap iteration order never affects its result - safe to allow,
// same reasoning as the existing #[allow(...)] elsewhere in this file.
#[allow(rustc::potential_query_instability)]
fn compute_edits<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    store: &Store,
    hash: DefPathHash,
    caller_genargs: ty::GenericArgsRef<'tcx>,
    default: &Body<'tcx>,
) -> Vec<(usize, Edit)> {
    // compute_edits runs for every single monomorphized function/
    // Instance codegen'd across the entire program (called from
    // rewrite_monomorphized, itself called unconditionally from
    // codegen_mir) - not just ones genuinely relevant to whatever
    // dispatch sites discovery actually found. The overwhelming
    // majority of functions in any real program - including
    // compiler/std-generated code that has nothing to do with the
    // program's own source at all, e.g. std::rt::lang_start's own
    // internal closure - have no entry in the store whatsoever. Bail
    // out here, before ever touching caller_genargs, rather than
    // paying the hashing cost (and risking the panic below) for
    // something this function was never going to apply to anyway.
    if !store.targets.keys().chain(store.tags.keys()).any(|(h, _, _)| *h == hash) {
        return Vec::new();
    }

    // If the caller's own generic args can't be hashed, apply no edits to
    // this function at all. The analysis side uses the same scheme
    // (rustc_verifopt::hash_args) on the same args, so it will have failed
    // identically and written no entry for this instantiation; falling back
    // to a coarser key instead could pick up another instantiation's entry.
    let Some(caller_genargs_hash) = hash_args(tcx, caller_genargs, &SHAPES) else {
        debug!(
            "[verifopt debug][compute_edits] could not hash caller generic args for {hash:?} \
             ({caller_genargs:?}) - leaving its dispatch sites untouched"
        );
        return Vec::new();
    };

    default
        .basic_blocks
        .indices()
        .filter_map(|bb| {
            let key = &(hash, bb.as_usize(), caller_genargs_hash.clone());

            let tags = store.tags.get(key);
            let targets = store.targets.get(key)?;

            if targets.len() == 1
                && store.exact.contains(key)
                && let Some(args) = &targets[0].1
            {
                // a provably single target, given as an exact instance
                Some((bb.as_usize(), Edit::SingleExact(targets[0].0, args.clone())))
            } else if targets.len() == 1 {
                // directly swap terminator
                Some((bb.as_usize(), Edit::Single(targets[0].0, targets[0].1.clone())))
            } else if let Some(tags) = tags {
                // tag dyn casts and switchint
                Some((bb.as_usize(), Edit::Tagged(tags.to_vec())))
            } else if targets.len() > 1 && targets.len() <= max_pointers_candidates() {
                // direct conditionals on pointers
                Some((bb.as_usize(), Edit::Pointers(targets.to_vec())))
            } else if targets.len() > max_pointers_candidates() {
                // Too many targets for a Pointers rewrite: left as the dyn call.
                // Recorded, so the cost of the limit (--max-candidates) is visible.
                log_skip(
                    tcx,
                    instance,
                    bb,
                    "too_many_targets",
                    &format!("{} targets > max {}", targets.len(), max_pointers_candidates()),
                );
                log_edit_kind(&format!("skipped too_many_targets n={}", targets.len()));
                None
            } else {
                // leave vtable dyn call
                None
            }
        })
        .collect()
}

/// One line per dispatch site the rewrite leaves alone, in a fixed format so a
/// build log can be tallied by crate and reason:
///
///   [verifopt skip] crate=<crate being compiled> reason=<code> site=<caller instance> bb<N>: <detail>
///
/// `crate` is the crate being *compiled*, which for a generic function is the
/// instantiating crate, not the one that defines it - the caller's own path
/// (e.g. `kernel::..`) names the latter. Reason codes: `receiver` (not a
/// reference/raw pointer), `unresolved` (a target can't be named here),
/// `unlinkable`, `check_site` (other resolution failure), `not_dyn`,
/// `vtable_slot`, `tagged_casts` (the planned tag sites aren't the casts
/// feeding this dispatch within this function), `not_call`, `not_virtual`
/// (the call at the stored block isn't a dynamic dispatch - see the safety
/// check in apply_edits).
fn log_skip(tcx: TyCtxt<'_>, instance: Instance<'_>, bb: BasicBlock, reason: &str, detail: &str) {
    debug!(
        "[verifopt skip] crate={} reason={} site={} {:?}: {}",
        tcx.crate_name(LOCAL_CRATE),
        reason,
        ty::print::with_no_trimmed_paths!(instance.to_string()),
        bb,
        detail
    );
}

/// One concrete function a Pointers rewrite can compare against and call: the
/// resolved instance, its callee operand, and the Self type to narrow the
/// receiver to.
#[derive(Clone)]
struct Cand<'tcx> {
    instance: Instance<'tcx>,
    fnc: Operand<'tcx>,
    self_ty: Ty<'tcx>,
}

/// What apply_edits actually emits for a site, decided before touching the
/// body (see the comment above the `plan` computation).
enum Plan<'tcx> {
    /// One direct call: the callee, the receiver's concrete Self type, and the
    /// edit-kind label to log ("single", or "single exact" for a target proven
    /// single by CHAmax).
    Single(Operand<'tcx>, Ty<'tcx>, &'static str),
    /// The candidates to compare against, and how many were found before
    /// truncation to max_pointers_candidates().
    Pointers(Vec<Cand<'tcx>>, usize),
    Tagged(Vec<(usize, usize, u64, DefPathHash, Option<Vec<DefPathHash>>)>),
}

fn apply_edits<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    default: Body<'tcx>,
    edits: Vec<(usize, Edit)>,
) -> Body<'tcx> {
    if edits.is_empty() {
        return default;
    }

    let linkable = Linkable::new(tcx, instance);

    let mut body = default.clone();

    dump_body(tcx, instance, &body, "before");

    let local_decls = body.local_decls.clone();
    let mut bbs = body.basic_blocks_mut().to_owned();

    for (bb_idx, edit) in edits {
        let bb = BasicBlock::from_usize(bb_idx);

        let (defid, gen_args, args, dest, target, unwind, call_source, source_info, span) = {
            let term = bbs[bb].terminator();
            let TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                ..
            } = &term.kind
            else {
                log_skip(tcx, instance, bb, "not_call", "terminator is not a Call");
                continue;
            };
            let (defid, gen_args) = match func {
                Operand::Constant(c) => match c.const_.ty().kind() {
                    FnDef(defid, a) => (*defid, *a), // *a: &'tcx List is Copy
                    _ => {
                        log_skip(tcx, instance, bb, "not_call", "callee is not an FnDef");
                        continue;
                    }
                },
                _ => {
                    log_skip(tcx, instance, bb, "not_call", "callee is not a constant");
                    continue;
                }
            };
            (
                defid,
                gen_args,
                args.clone(),
                *destination,
                *target,
                *unwind,
                *call_source,
                term.source_info,
                term.source_info.span,
            )
        };

        // Decide up front whether the receiver can be narrowed at all, so an
        // unsupported receiver bails out before any statements are emitted.
        let recv_ty = args[0].node.ty(&local_decls, tcx);
        let Some(recv_kind) = RecvKind::of(recv_ty) else {
            log_skip(tcx, instance, bb, "receiver", &format!("unsupported receiver type {recv_ty:?}"));
            continue;
        };

        // Safety check, part 1: the call at this block must really be a
        // dynamic dispatch - a trait method on a `dyn` receiver, which
        // resolves to a vtable call. Store entries are keyed by basic-block
        // index, so a store that doesn't match this code (the source changed
        // since the analysis - e.g. a new `#[inline]` letting the MIR inliner
        // renumber a caller's blocks - or a different toolchain or flags) can
        // point at an unrelated call. Without this, a Single edit would
        // replace that call with a direct call to the recorded target - a
        // miscompile rather than a skip. (Part 2, that every target
        // implements the dispatched method, is in fn_op.)
        match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), defid, gen_args) {
            Ok(Some(callee)) if matches!(callee.def, InstanceKind::Virtual(..)) => {}
            other => {
                log_skip(
                    tcx,
                    instance,
                    bb,
                    "not_virtual",
                    &format!("callee {defid:?} resolves to {other:?}, not a dynamic dispatch"),
                );
                continue;
            }
        }

        // Decide what to emit, still before touching the body. Only Single has
        // no fallback, so only it must get every target exactly right. A
        // Pointers rewrite compares the vtable slot against each candidate and
        // otherwise makes the original dyn call - so it's correct for *any*
        // subset of the real targets, and a candidate that can't be resolved
        // or linked here is dropped rather than sinking the whole site. That
        // is what lets the rest of this work:
        //
        // - a generic target with no recorded args (a CHA fallback candidate:
        //   the analysis couldn't trace the receiver, and CHA knows which
        //   impls exist but not how they're instantiated) is expanded into
        //   every instance of it compiled in this crate (Linkable::candidates_for);
        // - a Single whose one target can't be built that way becomes a
        //   Pointers over its expansion;
        // - a Tagged site whose tag sites aren't the casts feeding this
        //   dispatch in this function (the usual case when trait objects are
        //   created far from where they're used, e.g. during board setup), or
        //   whose targets don't all resolve, becomes a Pointers over the same
        //   targets instead of being skipped.
        let skip = |reason: &str, why: &str| {
            // Kept for existing greps; log_skip is the tallyable form.
            debug!(
                "[verifopt debug][apply_edits] leaving {:?} {:?} unrewritten: {}",
                instance.def_id(),
                bb,
                why
            );
            log_skip(tcx, instance, bb, reason, why);
        };
        let pointers_plan = |targets: &[(DefPathHash, Option<Vec<DefPathHash>>)]| -> Result<Plan<'tcx>, String> {
            let (cands, found) =
                linkable.pointer_candidates(instance, bb, defid, gen_args, span, targets)?;
            Ok(Plan::Pointers(cands, found))
        };
        let plan = match edit {
            Edit::Single(hash, self_hash) => {
                match linkable.check_site(defid, gen_args, span, &[(hash, self_hash.clone())], false) {
                    Ok(()) => match fn_op(tcx, defid, hash, self_hash.clone(), gen_args, span) {
                        Ok((fnc, self_ty)) => Ok(Plan::Single(fnc, self_ty, "single")),
                        Err(()) => Err(format!("target {hash:?} could not be resolved")),
                    },
                    Err(why) => pointers_plan(&[(hash, self_hash)]).map_err(|_| why),
                }
            }
            Edit::SingleExact(hash, arg_hashes) => linkable
                .exact_candidate(defid, span, hash, &arg_hashes)
                .map(|c| Plan::Single(c.fnc, c.self_ty, "single exact")),
            Edit::Pointers(targets) => pointers_plan(&targets),
            Edit::Tagged(sites) => {
                let targets: Vec<(DefPathHash, Option<Vec<DefPathHash>>)> = {
                    let mut t = Vec::new();
                    for (_, _, _, h, s) in &sites {
                        if !t.contains(&(*h, s.clone())) {
                            t.push((*h, s.clone()));
                        }
                    }
                    t
                };
                let casts_match = match &args[0].node {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                        let preds = default.basic_blocks.predecessors();
                        let found =
                            find_casts(
                                &bbs,
                                preds,
                                bb_idx,
                                p.local,
                                Some(bbs[bb].statements.len()),
                                &mut HashSet::default(),
                            );
                        let planned: HashSet<(usize, usize)> =
                            sites.iter().map(|(bb, stmt, _, _, _)| (*bb, *stmt)).collect();
                        found.as_ref() == Some(&planned)
                    }
                    _ => false,
                };
                if casts_match && linkable.check_site(defid, gen_args, span, &targets, false).is_ok() {
                    Ok(Plan::Tagged(sites))
                } else {
                    debug!(
                        "[verifopt debug][apply_edits] {:?} {:?}: Tagged not applicable (casts_match={}), trying Pointers",
                        instance.def_id(),
                        bb,
                        casts_match
                    );
                    pointers_plan(&targets)
                }
            }
        };
        let plan = match plan {
            Ok(plan) => plan,
            Err(why) => {
                let reason = if why.contains("could not be resolved") {
                    "unresolved"
                } else if why.contains("not linkable") {
                    "unlinkable"
                } else if why.contains("no candidates") {
                    "no_candidates"
                } else {
                    "check_site"
                };
                skip(reason, &why);
                continue;
            }
        };

        match plan {
            Plan::Single(fnc, self_ty, kind) => {

                let (recv, new_stmts) = narrow_dyn(
                    tcx,
                    &mut body,
                    source_info,
                    args[0].node.clone(),
                    recv_kind,
                    self_ty,
                    span,
                );
                bbs[bb].statements.extend(new_stmts);

                let mut new_args = args.clone();
                new_args[0].node = Operand::Move(recv);

                if let TerminatorKind::Call { func, args: a, .. } =
                    &mut bbs[bb].terminator_mut().kind
                {
                    *func = fnc;
                    *a = new_args;
                    log_edit_kind(kind);
                }
            }

            Plan::Pointers(cands, found) => {
                let _ = CRATE_NAME.get_or_init(|| tcx.crate_name(LOCAL_CRATE).to_string());

                let op = args[0].node.clone();

                let recv_ty = op.ty(&local_decls, tcx); // &dyn X
                let pointee_ty = recv_ty.builtin_deref(true).unwrap(); // dyn X

                // <dyn X as X>
                let trait_ref = match pointee_ty.kind() {
                    ty::Dynamic(preds, _) => {
                        DYNAMIC_HITS.fetch_add(1, Ordering::Relaxed);
                        let principal = preds.principal().unwrap();
                        principal.with_self_ty(tcx, pointee_ty).skip_binder()
                    }
                    _ => {
                        log_skip(tcx, instance, bb, "not_dyn", &format!("receiver pointee {pointee_ty:?} is not dyn"));
                        continue;
                    }
                };

                let pointee_trait = tcx.require_lang_item(LangItem::PointeeTrait, span);
                let metadata_assoc = tcx
                    .associated_items(pointee_trait)
                    .in_definition_order()
                    .find(|it| matches!(it.kind, AssocKind::Type { .. }))
                    .unwrap()
                    .def_id;

                // <dyn X as Pointee>::Metadata
                let proj =
                    Ty::new_projection(tcx, metadata_assoc, tcx.mk_args(&[pointee_ty.into()]));

                let meta_ty = match tcx
                    .try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), proj)
                {
                    Ok(ty) => ty, // DynMetadata<dyn X>
                    Err(_) => continue,
                };
                let raw_ptr_ty = Ty::new_ptr(tcx, tcx.types.unit, Mutability::Not); // *const ()

                // DynMetadata<dyn X>
                let meta_place = Place::from(body.local_decls.push(LocalDecl::new(meta_ty, span)));
                bbs[bb].statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        meta_place,
                        Rvalue::UnaryOp(UnOp::PtrMetadata, op),
                    ))),
                ));

                // raw *const ()
                let vt_ptr_place =
                    Place::from(body.local_decls.push(LocalDecl::new(raw_ptr_ty, span)));
                bbs[bb].statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        vt_ptr_place,
                        Rvalue::Cast(CastKind::Transmute, Operand::Move(meta_place), raw_ptr_ty),
                    ))),
                ));

                let entries = tcx.vtable_entries(trait_ref);
                let slot_idx = entries
                    .iter()
                    .position(|e| {
                        matches!(
                            e, VtblEntry::Method(inst) if inst.def_id() == defid
                        )
                    })
                    .unwrap();

                let VtblEntry::Method(vtable_instance) = &entries[slot_idx] else {
                    log_skip(tcx, instance, bb, "vtable_slot", "vtable slot is not a method");
                    continue;
                };

                let fn_abi_ty = vtable_instance.ty(tcx, TypingEnv::fully_monomorphized());
                let fn_sig = fn_abi_ty.fn_sig(tcx);
                let fn_ptr_ty = Ty::new_fn_ptr(tcx, fn_sig);

                let vt_typed_ty = Ty::new_ptr(tcx, fn_ptr_ty, Mutability::Not);

                // *const (fn ptr)
                let vt_slots_place =
                    Place::from(body.local_decls.push(LocalDecl::new(vt_typed_ty, span)));
                bbs[bb].statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        vt_slots_place,
                        Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(vt_ptr_place), vt_typed_ty),
                    ))),
                ));

                let op = Box::new(ConstOperand {
                    span: span,
                    user_ty: None,
                    const_: Const::from_usize(tcx, slot_idx.try_into().unwrap()),
                });

                // vtable as slots + slot idx
                let slot_ptr_loc = body.local_decls.push(LocalDecl::new(vt_typed_ty, span));
                let slot_ptr_place = Place::from(slot_ptr_loc);

                bbs[bb].statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        slot_ptr_place,
                        Rvalue::BinaryOp(
                            BinOp::Offset,
                            Box::new((Operand::Copy(vt_slots_place), Operand::Constant(op))),
                        ),
                    ))),
                ));

                let deref_place = Place {
                    local: slot_ptr_loc,
                    projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                };

                // loaded fn
                let slot_fn_place =
                    Place::from(body.local_decls.push(LocalDecl::new(fn_ptr_ty, span)));
                bbs[bb].statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        slot_fn_place,
                        Rvalue::Use(Operand::Copy(deref_place)),
                    ))),
                ));

                let is_cleanup = bbs[bb].is_cleanup;
                let mut orig = bbs[bb].terminator().clone();
                if let TerminatorKind::Call { target: t, .. } = &mut orig.kind {
                    *t = call_guard(&mut bbs, *t, source_info, is_cleanup);
                }
                let mut fallback = bbs.push(BasicBlockData::new_stmts(vec![], Some(orig), false));
                let n = cands.len();

                for (i, Cand { fnc, self_ty, .. }) in cands.iter().enumerate() {
                    let self_ty = *self_ty;

                    let (recv, new_stmts) = narrow_dyn(
                        tcx,
                        &mut body,
                        source_info,
                        args[0].node.clone(),
                        recv_kind,
                        self_ty,
                        span,
                    );
                    let mut new_args = args.clone();
                    new_args[0].node = Operand::Move(recv);

                    // Each arm's call needs its own return block (see call_guard).
                    let arm_target = call_guard(&mut bbs, target, source_info, is_cleanup);
                    let call_bb = bbs.push(BasicBlockData::new_stmts(
                        new_stmts,
                        Some(Terminator {
                            source_info,
                            kind: TerminatorKind::Call {
                                func: fnc.clone(),
                                args: new_args,
                                destination: dest,
                                target: arm_target,
                                unwind: unwind,
                                call_source: call_source,
                                fn_span: span,
                            },
                        }),
                        false,
                    ));

                    let cand_ptr_place =
                        Place::from(body.local_decls.push(LocalDecl::new(fn_ptr_ty, span)));
                    bbs[bb].statements.push(Statement::new(
                        source_info,
                        StatementKind::Assign(Box::new((
                            cand_ptr_place,
                            Rvalue::Cast(
                                CastKind::PointerCoercion(
                                    PointerCoercion::ReifyFnPointer(Safety::Unsafe),
                                    CoercionSource::AsCast,
                                ),
                                fnc.clone(),
                                fn_ptr_ty,
                            ),
                        ))),
                    ));

                    let eq_place =
                        Place::from(body.local_decls.push(LocalDecl::new(tcx.types.bool, span)));

                    let eq_stmt = Statement::new(
                        source_info,
                        StatementKind::Assign(Box::new((
                            eq_place,
                            Rvalue::BinaryOp(
                                BinOp::Eq,
                                Box::new((
                                    Operand::Copy(slot_fn_place),
                                    Operand::Copy(cand_ptr_place),
                                )),
                            ),
                        ))),
                    );

                    let new_term = Terminator {
                        source_info,
                        kind: TerminatorKind::SwitchInt {
                            discr: Operand::Copy(eq_place),
                            targets: SwitchTargets::static_if(1, call_bb, fallback),
                        },
                    };

                    if i == n - 1 {
                        bbs[bb].statements.push(eq_stmt);
                        bbs[bb].terminator = Some(new_term);
                    } else {
                        fallback = bbs.push(BasicBlockData::new_stmts(
                            vec![eq_stmt],
                            Some(new_term),
                            false,
                        ));
                    }
                }
                // `n` candidates, each a direct call guarded by a vtable-slot
                // comparison. (Every Pointers rewrite also keeps the original
                // dyn call as the fallback when none matches.)
                // When the list was truncated to max_pointers_candidates(),
                // `of=` says how many there were: the rest take the fallback.
                if found > n {
                    log_edit_kind(&format!("pointers n={n} of={found}"));
                } else {
                    log_edit_kind(&format!("pointers n={n}"));
                }
            }

            Plan::Tagged(sites) => {
                let recv_local = match &args[0].node {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
                    _ => continue,
                };

                let preds = default.basic_blocks.predecessors();

                let found = find_casts(
                    &bbs,
                    preds,
                    bb_idx,
                    recv_local,
                    Some(bbs[bb].statements.len()),
                    &mut HashSet::default(),
                );

                let planned: HashSet<(usize, usize)> = sites
                    .iter()
                    .map(|(bb, stmt, _, _, _)| (*bb, *stmt))
                    .collect();
                if found.as_ref() != Some(&planned) {
                    log_skip(
                        tcx,
                        instance,
                        bb,
                        "tagged_casts",
                        &format!(
                            "casts found in this function {:?} != planned tag sites {:?}",
                            found, planned
                        ),
                    );
                    continue;
                }

                let tag_local = body.local_decls.push(LocalDecl::new(tcx.types.usize, span));

                // Insert each tag assignment right after its cast. Latest
                // position first, so an insertion never shifts the index of a
                // cast still to be handled in the same block.
                let mut tag_sites: Vec<(usize, usize, u64)> =
                    sites.iter().map(|(b, i, t, _, _)| (*b, *i, *t)).collect();
                tag_sites.sort_by(|a, b| (b.0, b.1).cmp(&(a.0, a.1)));
                for (bb_idx, stmt_idx, tag) in &tag_sites {
                    let cb = BasicBlock::from_usize(*bb_idx);

                    bbs[cb].statements.insert(
                        stmt_idx + 1,
                        Statement::new(
                            source_info,
                            StatementKind::Assign(Box::new((
                                Place::from(tag_local),
                                Rvalue::Use(Operand::Constant(Box::new(ConstOperand {
                                    span,
                                    user_ty: None,
                                    const_: Const::from_usize(tcx, *tag),
                                }))),
                            ))),
                        ),
                    );
                }

                // Defence in depth: start the tag at a value no arm uses, at
                // function entry. find_casts only accepts the site if every path
                // to the dispatch passes one of the casts above, but if a path
                // were ever missed, the switch below would read this sentinel and
                // take the original dyn call - instead of reading an
                // uninitialized local, which would be undefined behaviour.
                let no_tag = tcx.data_layout.pointer_size().unsigned_int_max() as u64;
                bbs[START_BLOCK].statements.insert(
                    0,
                    Statement::new(
                        source_info,
                        StatementKind::Assign(Box::new((
                            Place::from(tag_local),
                            Rvalue::Use(Operand::Constant(Box::new(ConstOperand {
                                span,
                                user_ty: None,
                                const_: Const::from_usize(tcx, no_tag),
                            }))),
                        ))),
                    ),
                );

                let is_cleanup = bbs[bb].is_cleanup;
                let mut orig = bbs[bb].terminator().clone();
                if let TerminatorKind::Call { target: t, .. } = &mut orig.kind {
                    *t = call_guard(&mut bbs, *t, source_info, is_cleanup);
                }
                let fallback = bbs.push(BasicBlockData::new_stmts(vec![], Some(orig), false));

                let mut arms = Vec::new();
                // One arm per *tag*, not per cast site: the analysis gives each
                // implementation one tag, so several casts to the same type
                // share it - and a switch with duplicate values is invalid MIR
                // (and an invalid LLVM `switch`).
                let mut tags_with_arm: HashSet<u64> = HashSet::default();

                for (_, _, tag, impl_hash, self_hash) in &sites {
                    if !tags_with_arm.insert(*tag) {
                        continue;
                    }
                    let (fnc, self_ty) =
                        match fn_op(tcx, defid, *impl_hash, self_hash.clone(), gen_args, span) {
                            Ok(v) => v,
                            Err(_) => continue,
                        };
                    let (recv, stmts) = narrow_dyn(
                        tcx,
                        &mut body,
                        source_info,
                        args[0].node.clone(),
                        recv_kind,
                        self_ty,
                        span,
                    );

                    let mut new_args = args.clone();
                    new_args[0].node = Operand::Move(recv);

                    // Each arm's call needs its own return block (see call_guard).
                    let arm_target = call_guard(&mut bbs, target, source_info, is_cleanup);
                    let cb = bbs.push(BasicBlockData::new_stmts(
                        stmts,
                        Some(Terminator {
                            source_info,
                            kind: TerminatorKind::Call {
                                func: fnc,
                                args: new_args,
                                destination: dest,
                                target: arm_target,
                                unwind,
                                call_source,
                                fn_span: span,
                            },
                        }),
                        false,
                    ));
                    arms.push((*tag as u128, cb));
                }

                // One direct call per arm; any other tag value (including the
                // entry sentinel) takes the original dyn call.
                let n = arms.len();
                bbs[bb].terminator = Some(Terminator {
                    source_info,
                    kind: TerminatorKind::SwitchInt {
                        discr: Operand::Copy(Place::from(tag_local)),
                        targets: SwitchTargets::new(arms.into_iter(), fallback),
                    },
                });
                log_edit_kind(&format!("tagged n={n}"));
            }
        }
    }

    *body.basic_blocks_mut() = bbs;

    dump_body(tcx, instance, &body, "after");

    //tcx.arena.alloc(body)
    body
}

/// Safe wrapper around tcx.def_path_hash_to_def_id - that function's
/// own internal hook (def_path_hash_to_def_id_extern, in
/// rustc_metadata's own cstore_impl.rs) calls bug!() outright
/// ("uninterned StableCrateId") if hash's own crate was never loaded
/// into this compilation session at all, rather than returning None
/// gracefully - so wrapping it in .ok_or(())? or .unwrap() doesn't
/// actually protect anything, since the panic happens *inside* the
/// call, before it would ever get a chance to return at all.
///
/// This situation isn't a rare edge case here: a dependency crate's
/// own compilation session never loads a downstream consumer's own
/// crate metadata at all (that would be a circular dependency, which
/// cargo/rustc themselves never allow to exist in the first place) -
/// so a rewrite whose target type is only ever defined in a downstream
/// consumer of the crate currently being compiled will always hit this,
/// deterministically, every time. Checking tcx.untracked().
/// stable_crate_ids first - the same map the internal hook itself
/// reads from, just without the panic-on-miss - lets this decline
/// gracefully (leaving the original, vtable-based dyn call in place)
/// rather than crashing the whole compilation.

/// Which functions code in the caller's codegen unit(s) can reference.
///
/// The rewrite adds direct calls (and, for Pointers, function-pointer
/// references) that the monomorphization collector never saw - it ran on the
/// original MIR, before this rewrite. So a target the store names can be:
///
/// - never instantiated at all: e.g. a spurious candidate like
///   `<Box<Counter> as Iterator>::next` when no `Box<Counter>` is ever turned
///   into a trait object. Referencing it is an "undefined reference" at link
///   time (seen in `box_dyn_iter`'s debug build).
/// - instantiated only in another codegen unit, with internal linkage:
///   partitioning internalizes items whose collected uses are all in one CGU,
///   and gives inline/LocalCopy items copies only in the CGUs that need them.
/// - in an upstream crate, but not exported.
///
/// In all these cases the whole site keeps its dyn call. Dropping just the
/// arm would only be sound if the target could never be the runtime callee,
/// which a crate-local check can't establish: an upstream crate's vtables can
/// point at functions this crate never compiles.
struct Linkable<'tcx> {
    tcx: TyCtxt<'tcx>,
    all_cgus: &'tcx [CodegenUnit<'tcx>],
    /// Every CGU the caller is codegenned in (several if it's a LocalCopy
    /// item); the rewritten body is emitted into each of them.
    caller_cgus: Vec<&'tcx CodegenUnit<'tcx>>,
}

impl<'tcx> Linkable<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, caller: Instance<'tcx>) -> Self {
        let all_cgus = tcx.collect_and_partition_mono_items(()).codegen_units;
        let caller_item = MonoItem::Fn(caller);
        let caller_cgus =
            all_cgus.iter().filter(|cgu| cgu.items().contains_key(&caller_item)).collect();
        Linkable { tcx, all_cgus, caller_cgus }
    }

    fn can_reference(&self, target: Instance<'tcx>) -> bool {
        let item = MonoItem::Fn(target);

        // Instantiated somewhere in this crate with a linkage other CGUs can
        // see (External, with Default or Hidden visibility - same link unit).
        if self
            .all_cgus
            .iter()
            .any(|cgu| cgu.items().get(&item).is_some_and(|d| d.linkage != Linkage::Internal))
        {
            return true;
        }

        // Only internal copies (or none): fine iff every CGU the caller is
        // emitted into has its own copy.
        if !self.caller_cgus.is_empty()
            && self.caller_cgus.iter().all(|cgu| cgu.items().contains_key(&item))
        {
            return true;
        }

        // Provided by an upstream crate: an exported non-generic item, or a
        // shared generic instance (share-generics).
        let did = target.def_id();
        if did.is_local() {
            return false;
        }
        if target.args.non_erasable_generics().next().is_some() {
            target.upstream_monomorphization(self.tcx).is_some()
        } else {
            matches!(target.def, InstanceKind::Item(_)) && self.tcx.is_reachable_non_generic(did)
        }
    }

    /// The concrete functions a Pointers rewrite may use for one recorded
    /// target, each resolved and linkable from here:
    /// - the recorded target itself, if its instance can be built (fn_op);
    /// - otherwise, for a generic target recorded without generic args (a
    ///   CHA fallback candidate), every instance of it compiled in this crate.
    ///   Each is a real implementation of the dispatched method for its own
    ///   Self type; which one (if any) the object actually has is decided at
    ///   runtime by the vtable-slot comparison, so any of them is safe to
    ///   offer.
    fn candidates_for(
        &self,
        orig_callee: DefId,
        gen_args: &'tcx List<GenericArg<'tcx>>,
        span: Span,
        hash: DefPathHash,
        self_hashes: &Option<Vec<DefPathHash>>,
    ) -> Result<Vec<Cand<'tcx>>, String> {
        let tcx = self.tcx;
        let env = TypingEnv::fully_monomorphized();

        if let Ok((fnc, self_ty)) = fn_op(tcx, orig_callee, hash, self_hashes.clone(), gen_args, span) {
            let Operand::Constant(c) = &fnc else {
                return Err(format!("target {hash:?} is not a constant fn operand"));
            };
            let ty::FnDef(did, args) = *c.const_.ty().kind() else {
                return Err(format!("target {hash:?} is not an FnDef"));
            };
            let instance = match Instance::try_resolve(tcx, env, did, args) {
                Ok(Some(i)) => i,
                _ => return Err(format!("target {did:?} does not resolve to an instance")),
            };
            self.check_pointer_target(instance, did, args)?;
            return Ok(vec![Cand { instance, fnc, self_ty }]);
        }

        // No usable args recorded: expand a generic target into its local instances.
        let expandable = self_hashes.is_none()
            && def_id_from_hash(tcx, hash).is_some_and(|did| {
                !tcx.is_closure_like(did) && tcx.generics_of(did).count() > 0
            });
        if !expandable {
            return Err(format!("target {hash:?} could not be resolved"));
        }
        let did = def_id_from_hash(tcx, hash).unwrap();
        if !implements_dispatched_method(tcx, did, orig_callee) {
            return Err(format!(
                "target {did:?} does not implement the dispatched method {orig_callee:?}"
            ));
        }
        let mut out: Vec<Cand<'tcx>> = Vec::new();
        for cgu in self.all_cgus {
            for item in cgu.items().keys() {
                let MonoItem::Fn(inst) = *item else { continue };
                if inst.def_id() != did
                    || !matches!(inst.def, InstanceKind::Item(_))
                    || out.iter().any(|c| c.instance == inst)
                {
                    continue;
                }
                let parent = tcx.parent(did);
                let raw_self_ty = if tcx.def_kind(parent) == DefKind::Trait {
                    inst.args.type_at(0)
                } else {
                    tcx.type_of(parent).instantiate(tcx, inst.args)
                };
                let Ok(self_ty) = tcx.try_normalize_erasing_regions(env, raw_self_ty) else {
                    continue;
                };
                if self.check_pointer_target(inst, did, inst.args).is_err() {
                    continue;
                }
                let fnc = Operand::Constant(Box::new(ConstOperand {
                    span,
                    user_ty: None,
                    const_: Const::zero_sized(Ty::new_fn_def(tcx, did, inst.args)),
                }));
                out.push(Cand { instance: inst, fnc, self_ty });
            }
        }
        if out.is_empty() {
            return Err(format!(
                "target {hash:?} could not be resolved, and no linkable instance of {did:?} is compiled in this crate"
            ));
        }
        debug!(
            "[verifopt debug][apply_edits] expanded generic target {:?} (no recorded args) into {} local instance(s)",
            did,
            out.len()
        );
        Ok(out)
    }

    /// The exact instance a Store::exact site names: the function and its own
    /// generic args, built as is (no trait-based resolution - that reads
    /// recorded args as the Self ADT's, which an instance's own args aren't),
    /// then subjected to the same checks as any target: it implements the
    /// dispatched method, resolves to exactly that function, and is linkable.
    fn exact_candidate(
        &self,
        orig_callee: DefId,
        span: Span,
        hash: DefPathHash,
        arg_hashes: &[DefPathHash],
    ) -> Result<Cand<'tcx>, String> {
        let tcx = self.tcx;
        let env = TypingEnv::fully_monomorphized();
        let Some(did) = def_id_from_hash(tcx, hash) else {
            return Err(format!("target {hash:?} could not be resolved"));
        };
        if !implements_dispatched_method(tcx, did, orig_callee) {
            return Err(format!(
                "target {did:?} does not implement the dispatched method {orig_callee:?}"
            ));
        }
        let Some(args) = arg_hashes
            .iter()
            .map(|h| arg_from_hash(tcx, *h, &SHAPES))
            .collect::<Option<Vec<GenericArg<'tcx>>>>()
        else {
            return Err(format!("target {did:?}'s exact args could not be resolved"));
        };
        let args = tcx.mk_args(&args);
        if args.len() != tcx.generics_of(did).count() {
            return Err(format!("target {did:?}'s exact args could not be resolved (wrong count)"));
        }
        let instance = match Instance::try_resolve(tcx, env, did, args) {
            Ok(Some(i)) if i.def_id() == did => i,
            other => {
                return Err(format!("target {did:?} could not be resolved as exact instance: {other:?}"));
            }
        };
        if !self.can_reference(instance) {
            return Err(format!("target {instance:?} is not linkable from here"));
        }
        let parent = tcx.parent(did);
        let raw_self_ty = if tcx.def_kind(parent) == DefKind::Trait {
            args.type_at(0)
        } else {
            tcx.type_of(parent).instantiate(tcx, args)
        };
        let Ok(self_ty) = tcx.try_normalize_erasing_regions(env, raw_self_ty) else {
            return Err(format!("target {did:?}'s Self type could not be normalized"));
        };
        let fnc = Operand::Constant(Box::new(ConstOperand {
            span,
            user_ty: None,
            const_: Const::zero_sized(Ty::new_fn_def(tcx, did, args)),
        }));
        Ok(Cand { instance, fnc, self_ty })
    }

    /// For a Pointers candidate: the callee must be referenceable, and so must
    /// the function pointer compared against the vtable slot.
    fn check_pointer_target(
        &self,
        callee: Instance<'tcx>,
        did: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), String> {
        if !self.can_reference(callee) {
            return Err(format!("target {callee:?} is not linkable from here"));
        }
        match Instance::resolve_for_fn_ptr(self.tcx, TypingEnv::fully_monomorphized(), did, args) {
            Some(fp) if self.can_reference(fp) => Ok(()),
            Some(fp) => Err(format!("fn pointer {fp:?} is not linkable from here")),
            None => Err(format!("target {did:?} has no fn-pointer instance")),
        }
    }

    /// Every candidate for a Pointers rewrite of one site: each recorded
    /// target's candidates (see candidates_for), with targets that yield none
    /// dropped - sound, since unmatched objects take the original dyn call -
    /// deduplicated, and capped at max_pointers_candidates() (any subset is
    /// sound too). Err only if nothing at all is usable.
    fn pointer_candidates(
        &self,
        caller: Instance<'tcx>,
        bb: BasicBlock,
        orig_callee: DefId,
        gen_args: &'tcx List<GenericArg<'tcx>>,
        span: Span,
        targets: &[(DefPathHash, Option<Vec<DefPathHash>>)],
    ) -> Result<(Vec<Cand<'tcx>>, usize), String> {
        let mut cands: Vec<Cand<'tcx>> = Vec::new();
        let mut dropped: Vec<String> = Vec::new();
        for (hash, self_hashes) in targets {
            match self.candidates_for(orig_callee, gen_args, span, *hash, self_hashes) {
                Ok(found) => {
                    for c in found {
                        if !cands.iter().any(|x| x.instance == c.instance) {
                            cands.push(c);
                        }
                    }
                }
                Err(why) => dropped.push(why),
            }
        }
        for why in &dropped {
            debug!(
                "[verifopt drop] crate={} site={} {:?}: {}",
                self.tcx.crate_name(LOCAL_CRATE),
                ty::print::with_no_trimmed_paths!(caller.to_string()),
                bb,
                why
            );
        }
        if cands.is_empty() {
            return Err(format!(
                "no candidates left for Pointers: {}",
                dropped.first().map(String::as_str).unwrap_or("no targets")
            ));
        }
        let found = cands.len();
        let max = max_pointers_candidates();
        if cands.len() > max {
            debug!(
                "[verifopt debug][apply_edits] {:?} {:?}: {} candidates, keeping the first {}",
                caller.def_id(),
                bb,
                cands.len(),
                max
            );
            cands.truncate(max);
        }
        Ok((cands, found))
    }

    /// Resolves every target of a site the way codegen will, and checks each
    /// function it would reference: the callee, and for Pointers also the
    /// function pointer it compares against the vtable slot (which can be a
    /// different instance, e.g. a ReifyShim).
    fn check_site(
        &self,
        orig_callee: DefId,
        gen_args: &'tcx List<GenericArg<'tcx>>,
        span: Span,
        targets: &[(DefPathHash, Option<Vec<DefPathHash>>)],
        compares_fn_ptrs: bool,
    ) -> Result<(), String> {
        let env = TypingEnv::fully_monomorphized();
        for (hash, self_hashes) in targets {
            let Ok((fnc, _)) =
                fn_op(self.tcx, orig_callee, *hash, self_hashes.clone(), gen_args, span)
            else {
                return Err(format!("target {hash:?} could not be resolved"));
            };
            let Operand::Constant(c) = &fnc else {
                return Err(format!("target {hash:?} is not a constant fn operand"));
            };
            let ty::FnDef(did, args) = *c.const_.ty().kind() else {
                return Err(format!("target {hash:?} is not an FnDef"));
            };

            let callee = match Instance::try_resolve(self.tcx, env, did, args) {
                Ok(Some(i)) => i,
                _ => return Err(format!("target {did:?} does not resolve to an instance")),
            };
            if !self.can_reference(callee) {
                return Err(format!("target {callee:?} is not linkable from here"));
            }

            if compares_fn_ptrs {
                match Instance::resolve_for_fn_ptr(self.tcx, env, did, args) {
                    Some(fp) if self.can_reference(fp) => {}
                    Some(fp) => return Err(format!("fn pointer {fp:?} is not linkable from here")),
                    None => return Err(format!("target {did:?} has no fn-pointer instance")),
                }
            }
        }
        Ok(())
    }
}

/// Safety check, part 2: whether `target` can be what a dynamic dispatch of
/// `method` (a trait method) calls. True for the method's own default body,
/// for an impl item implementing exactly that trait method, and for a closure
/// or fn item dispatched through an Fn-family trait (they implement nothing
/// else). Anything else means the store entry doesn't describe this call -
/// e.g. the block now holds a different dyn call than the one analyzed - and
/// using it would call an unrelated function. Pointers rewrites would never
/// match such a target at runtime anyway, but Single and Tagged have no
/// runtime type check, so it's enforced for every edit kind (in fn_op, and in
/// Linkable::candidates_for's expansion).
fn implements_dispatched_method(tcx: TyCtxt<'_>, target: DefId, method: DefId) -> bool {
    if target == method {
        return true;
    }
    if tcx.is_closure_like(target) || matches!(tcx.def_kind(target), DefKind::Fn) {
        return tcx.trait_of_assoc(method).is_some_and(|t| {
            tcx.is_fn_trait(t) || tcx.async_fn_trait_kind_from_def_id(t).is_some()
        });
    }
    matches!(tcx.def_kind(target), DefKind::AssocFn)
        && tcx.associated_item(target).trait_item_def_id() == Some(method)
}

/// Resolves a non-closure dispatch target the way the vtable slot was filled:
/// build the concrete Self type, then resolve the *trait method* (the
/// original callee) with that Self and the call site's own trait/method args.
/// rustc's trait selection then returns the impl method with its correctly
/// ordered generic args - which the recorded hashes are not:
///
/// - for an impl method, the analysis records the *ADT's* args. Those equal
///   the impl's parameters only when the impl is exactly `impl<P..> Tr for
///   Adt<P..>`. `impl<B, I, F> Iterator for Map<I, F>` has an extra `B`;
///   tock's `impl<'a> Client for Foo` (Foo without a lifetime) has a
///   parameter the ADT doesn't; others reorder them.
/// - for a trait default method, it records only `[Self]`, but the method's
///   args are `[Self, <trait params>..]` - and nearly every tock HIL trait
///   has one (`Alarm<'a>`, `Client<'a>`, ...).
///
/// Both produced a wrong arg count ("FAILED at args.len() check"), so those
/// sites were never rewritten. Returns None (fall back to the recorded args)
/// when this doesn't apply: closure-like targets (handled separately below),
/// non-trait callees, impls whose Self isn't an ADT, or a selection result
/// that isn't the recorded target (then the store and rustc disagree, and
/// the caller's fallback decides).
fn resolve_target_via_trait<'tcx>(
    tcx: TyCtxt<'tcx>,
    orig_callee: DefId,
    target_did: DefId,
    self_hashes: &Option<Vec<DefPathHash>>,
    gen_args: &'tcx List<GenericArg<'tcx>>,
) -> Option<Instance<'tcx>> {
    if tcx.is_closure_like(target_did)
        || gen_args.is_empty()
        || tcx.trait_of_assoc(orig_callee).is_none()
    {
        return None;
    }
    let recorded: Vec<GenericArg<'tcx>> = match self_hashes {
        Some(hashes) => {
            hashes.iter().map(|h| arg_from_hash(tcx, *h, &SHAPES)).collect::<Option<_>>()?
        }
        None => Vec::new(),
    };

    let parent = tcx.parent(target_did);
    let self_ty = if tcx.def_kind(parent) == DefKind::Trait {
        // Default method: the recorded args are [Self].
        recorded.first()?.as_type()?
    } else {
        // Impl method: the recorded args are the Self ADT's own args.
        let ty::Adt(adt_def, _) = *tcx.type_of(parent).instantiate_identity().kind() else {
            return None;
        };
        if recorded.len() != tcx.generics_of(adt_def.did()).count() {
            return None;
        }
        Ty::new_adt(tcx, adt_def, tcx.mk_args(&recorded))
    };

    let callee_args = tcx.mk_args_from_iter(
        std::iter::once(GenericArg::from(self_ty)).chain(gen_args.iter().skip(1)),
    );
    match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), orig_callee, callee_args) {
        Ok(Some(inst)) if inst.def_id() == target_did => Some(inst),
        other => {
            debug!(
                "[verifopt debug][fn_op] resolving {:?} via {:?} with Self={:?} gave {:?}, not the recorded target",
                target_did, orig_callee, self_ty, other
            );
            None
        }
    }
}

fn fn_op<'tcx>(
    tcx: TyCtxt<'tcx>,
    // The DefId of the original (virtual) callee, e.g. FnMut::call_mut.
    // Needed for closure-like targets, whose DefId is not callable itself.
    orig_callee: DefId,
    hash: DefPathHash,
    self_hashes: Option<Vec<DefPathHash>>,
    gen_args: &'tcx List<GenericArg<'tcx>>,
    span: Span,
) -> Result<(Operand<'tcx>, Ty<'tcx>), ()> {
    let target_did = match def_id_from_hash(tcx, hash) {
        Some(did) => did,
        None => {
            debug!("[verifopt debug][fn_op] FAILED at target_did resolution, hash={:?}", hash);
            return Err(());
        }
    };

    if !implements_dispatched_method(tcx, target_did, orig_callee) {
        debug!(
            "[verifopt debug][fn_op] FAILED: target {:?} does not implement the dispatched method {:?}",
            target_did, orig_callee
        );
        return Err(());
    }

    let _ = CRATE_NAME.get_or_init(|| tcx.crate_name(LOCAL_CRATE).to_string());

    // Preferred: let rustc's trait selection pick the impl, the same way the
    // vtable slot was filled (see resolve_target_via_trait). The recorded
    // hashes are the *ADT's* (or, for a default method, just Self's) generic
    // args, which only coincide with the target method's own args when its
    // impl's parameters happen to be exactly the ADT's, in order.
    let instance = if let Some(inst) =
        resolve_target_via_trait(tcx, orig_callee, target_did, &self_hashes, gen_args)
    {
        FN_OP_ARGS_OK.fetch_add(1, Ordering::Relaxed);
        inst
    } else {
        let args = match &self_hashes {
            Some(hashes) => {
                // Each hash is one generic arg (lifetimes included, as a fixed
                // sentinel), so the rebuilt list has the target's own arity.
                let arg_list: Vec<GenericArg<'tcx>> = match hashes
                    .iter()
                    .map(|h| arg_from_hash(tcx, *h, &SHAPES).ok_or(()))
                    .collect::<Result<Vec<_>, ()>>()
                {
                    Ok(v) => v,
                    Err(_) => {
                        debug!("[verifopt debug][fn_op] FAILED at self_hashes -> args resolution, target_did={:?} self_hashes={:?}", target_did, self_hashes);
                        return Err(());
                    }
                };
                tcx.mk_args(&arg_list)
            }
            None => tcx.mk_args_from_iter(gen_args.iter().skip(1)),
        };

        if args.len() != tcx.generics_of(target_did).count() {
            debug!(
                "[verifopt debug][fn_op] FAILED at args.len() check: target_did={:?} args={:?} args.len()={:?} expected_count={:?}",
                target_did,
                args,
                args.len(),
                tcx.generics_of(target_did).count(),
            );
            FN_OP_ARGS_MISMATCH.fetch_add(1, Ordering::Relaxed);
            return Err(());
        }
        FN_OP_ARGS_OK.fetch_add(1, Ordering::Relaxed);

        match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), target_did, args) {
            Ok(Some(inst)) => inst,
            other => {
                debug!("[verifopt debug][fn_op] FAILED at Instance::try_resolve: target_did={:?} args={:?} result={:?}", target_did, args, other);
                return Err(());
            }
        }
    };

    let raw_self_ty = if tcx.is_closure_like(target_did) {
        // A closure's own tcx.parent() is just whatever function it's
        // defined inside - never a genuine self-type provider the way
        // an impl block or trait is - so neither branch below applies.
        // For a closure-like DefId, type_of *is* the closure / coroutine /
        // coroutine-closure type itself (instantiated with the closure's own,
        // already-resolved generic args), which is exactly the Self type we
        // want. This also covers coroutines, which Ty::new_closure did not.
        tcx.type_of(target_did).instantiate(tcx, instance.args)
    } else {
        let parent_did = tcx.parent(target_did);
        if tcx.def_kind(parent_did) == DefKind::Trait {
            match &self_hashes {
                Some(hashes) if !hashes.is_empty() => {
                    match arg_from_hash(tcx, hashes[0], &SHAPES).and_then(|a| a.as_type()) {
                        Some(ty) => ty,
                        None => {
                            debug!("[verifopt debug][fn_op] FAILED at self_did resolution (trait parent branch): target_did={:?} self_hashes={:?}", target_did, self_hashes);
                            return Err(());
                        }
                    }
                }
                _ => {
                    debug!("[verifopt debug][fn_op] FAILED: parent is a Trait but self_hashes is None/empty: target_did={:?} self_hashes={:?}", target_did, self_hashes);
                    return Err(());
                }
            }
        } else {
            tcx.type_of(parent_did).instantiate(tcx, instance.args)
        }
    };
    let self_ty = match tcx.try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), raw_self_ty)
    {
        Ok(ty) => ty,
        Err(_) => {
            debug!("[verifopt debug][fn_op] FAILED at self_ty normalization: target_did={:?} raw_self_ty={:?}", target_did, raw_self_ty);
            return Err(());
        }
    };

    // Build the callee operand. It must be a zero-sized FnDef constant.
    let fn_ty = if tcx.is_closure_like(target_did) {
        // instance.ty() for a closure-like instance is the closure type
        // itself (non-ZST whenever it captures anything), not a function
        // type. Emitting Const::zero_sized of it is what tripped
        // `assertion failed: layout.is_zst()` in OperandRef::zero_sized.
        //
        // Instead, call the original trait method (FnMut::call_mut etc.)
        // with Self replaced by the concrete closure type:
        //   <{closure} as FnMut<Args>>::call_mut
        // Codegen resolves that to the closure body (or a ClosureOnceShim
        // for call_once on an Fn/FnMut closure), i.e. the same thing the
        // vtable slot points at.
        if tcx.trait_of_assoc(orig_callee).is_none() || gen_args.is_empty() {
            debug!("[verifopt debug][fn_op] FAILED: closure-like target but original callee is not a trait method: target_did={:?} orig_callee={:?}", target_did, orig_callee);
            return Err(());
        }
        let callee_args = tcx.mk_args_from_iter(
            std::iter::once(GenericArg::from(self_ty)).chain(gen_args.iter().skip(1)),
        );
        match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), orig_callee, callee_args) {
            Ok(Some(resolved)) => {
                let points_at_target = match resolved.def {
                    InstanceKind::ClosureOnceShim { .. } => true,
                    _ => resolved.def_id() == target_did,
                };
                if !points_at_target {
                    debug!("[verifopt debug][fn_op] FAILED: <closure as Trait>::method resolved to an unexpected instance: target_did={:?} resolved={:?}", target_did, resolved);
                    return Err(());
                }
            }
            other => {
                debug!("[verifopt debug][fn_op] FAILED at closure callee resolution: orig_callee={:?} callee_args={:?} result={:?}", orig_callee, callee_args, other);
                return Err(());
            }
        }
        Ty::new_fn_def(tcx, orig_callee, callee_args)
    } else {
        instance.ty(tcx, TypingEnv::fully_monomorphized())
    };

    // Defensive: never emit a zero-sized constant whose type is not a ZST
    // function item, whatever the target turns out to be.
    if !matches!(fn_ty.kind(), FnDef(..)) {
        debug!("[verifopt debug][fn_op] FAILED: callee type is not an FnDef: target_did={:?} fn_ty={:?}", target_did, fn_ty);
        return Err(());
    }

    let op = Operand::Constant(Box::new(ConstOperand {
        span: span,
        user_ty: None,
        const_: Const::zero_sized(fn_ty),
    }));

    debug!("[verifopt debug][fn_op] SUCCESS: target_did={:?} self_ty={:?}", target_did, self_ty);
    Ok((op, self_ty))
}

/// How the original dyn receiver was passed. The narrowed receiver must
/// keep the same pointer kind and mutability, e.g. FnMut::call_mut takes
/// `&mut Self`, so narrowing `&mut dyn FnMut` to `&{closure}` would be
/// ill-typed MIR.
#[derive(Clone, Copy, Debug)]
enum RecvKind {
    Ref(Mutability),
    RawPtr(Mutability),
}

impl RecvKind {
    /// Only `&dyn`, `&mut dyn`, `*const dyn` and `*mut dyn` receivers can be
    /// narrowed with a pointer cast. Anything else (Box<Self>, Rc<Self>,
    /// Pin<&mut Self>, ...) is not handled, and the call is left as-is.
    fn of(recv_ty: Ty<'_>) -> Option<RecvKind> {
        match recv_ty.kind() {
            ty::Ref(_, _, m) => Some(RecvKind::Ref(*m)),
            ty::RawPtr(_, m) => Some(RecvKind::RawPtr(*m)),
            _ => None,
        }
    }
}

/// Returns a fresh block that just jumps to `target`, for use as the return
/// block of a call the rewrite creates.
///
/// Codegen stores a call's return value at the *start of its return block*
/// (block.rs: `do_call` -> `store_return`, emitted into `target`'s block for
/// an `invoke`). That is only valid because optimized MIR guarantees no
/// call's return edge is shared: AddCallGuards splits any critical call edge
/// with an empty `goto` block, exactly like this one. A rewrite that fans one
/// dispatch out into several calls - the Pointers/Tagged arms plus the
/// fallback - all returning to the original target breaks that invariant:
/// every call's store lands at the top of the shared block, each using a
/// value from a different predecessor. That's invalid IR (the LLVM verifier,
/// off in release builds, would reject it); in practice the stores collapse
/// to the last one codegen emitted, silently dropping the other calls'
/// results - seen as box_dyn_iter's `for` loop ending after one `next`,
/// whose `Some(1)` never reached the loop.
fn call_guard<'tcx>(
    bbs: &mut IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    target: Option<BasicBlock>,
    source_info: SourceInfo,
    is_cleanup: bool,
) -> Option<BasicBlock> {
    let target = target?;
    Some(bbs.push(BasicBlockData::new_stmts(
        vec![],
        Some(Terminator { source_info, kind: TerminatorKind::Goto { target } }),
        is_cleanup,
    )))
}

fn narrow_dyn<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    si: SourceInfo,
    recv: Operand<'tcx>,
    recv_kind: RecvKind,
    self_ty: Ty<'tcx>,
    span: Span,
) -> (Place<'tcx>, Vec<Statement<'tcx>>) {
    let mutbl = match recv_kind {
        RecvKind::Ref(m) | RecvKind::RawPtr(m) => m,
    };
    let ptr_ty = Ty::new_ptr(tcx, self_ty, mutbl);

    let mut stmts = Vec::new();

    let thin = Place::from(body.local_decls.push(LocalDecl::new(ptr_ty, span)));
    stmts.push(Statement::new(
        si,
        StatementKind::Assign(Box::new((
            thin,
            Rvalue::Cast(CastKind::PtrToPtr, recv, ptr_ty),
        ))),
    ));

    // Raw-pointer receivers are passed as the (now thin) raw pointer.
    if let RecvKind::RawPtr(_) = recv_kind {
        return (thin, stmts);
    }

    let deref = Place {
        local: thin.local,
        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
    };

    let ref_ty = Ty::new_ref(tcx, tcx.lifetimes.re_erased, self_ty, mutbl);
    let borrow_kind = match mutbl {
        Mutability::Not => BorrowKind::Shared,
        Mutability::Mut => BorrowKind::Mut { kind: MutBorrowKind::Default },
    };

    let out = Place::from(body.local_decls.push(LocalDecl::new(ref_ty, span)));
    stmts.push(Statement::new(
        si,
        StatementKind::Assign(Box::new((
            out,
            Rvalue::Ref(tcx.lifetimes.re_erased, borrow_kind, deref),
        ))),
    ));

    (out, stmts)
}

/// Whether `term` writes `local` itself - not just through a pointer stored
/// in it: a call's destination, an inline-asm output, a yield's resume arg.
fn terminator_writes(term: &Terminator<'_>, local: Local) -> bool {
    let writes = |p: &Place<'_>| {
        p.local == local && p.projection.first() != Some(&ProjectionElem::Deref)
    };
    match &term.kind {
        TerminatorKind::Call { destination, .. } => writes(destination),
        TerminatorKind::InlineAsm { operands, .. } => operands.iter().any(|op| match op {
            InlineAsmOperand::Out { place: Some(p), .. }
            | InlineAsmOperand::InOut { out_place: Some(p), .. } => writes(p),
            _ => false,
        }),
        TerminatorKind::Yield { resume_arg, .. } => writes(resume_arg),
        _ => false,
    }
}

/// The cast sites (block, statement index) that can have produced `local`'s
/// value at a point in block `bb_idx`: before statement `before`, or - with
/// `before == None` - at the end of the block, after its terminator.
///
/// Walks definitions backwards: an Unsize coercion is a cast site; a plain
/// copy/move continues with its source, from that statement's position; any
/// other definition - another rvalue, a projected write into the local, a
/// SetDiscriminant, or a terminator writing it (a call's destination, an
/// inline-asm output, a yield's resume arg) - means the value's origin isn't
/// a known cast, so the whole search is None. So is reaching the function's
/// entry without a definition (an argument). Revisiting a (block, local,
/// position) - a loop - contributes nothing new.
///
/// A Tagged rewrite is only valid if every path to the dispatch passes one of
/// the returned casts. Previously terminators weren't checked at all, so a
/// call that replaced the receiver after a cast went unnoticed (the switch
/// would then have used that cast's stale tag); and following a copy rescanned
/// its whole block, so a later redefinition of the copy's source in that block
/// could be mistaken for its origin.
// The only thing done with this result is a set-equality check, which only
// depends on set membership - completely unaffected by iteration or insertion order.
#[allow(rustc::potential_query_instability)]
fn find_casts<'tcx>(
    bbs: &IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    preds: &IndexVec<BasicBlock, SmallVec<[BasicBlock; 4]>>,
    bb_idx: usize,
    local: Local,
    before: Option<usize>,
    seen: &mut HashSet<(usize, Local, Option<usize>)>,
) -> Option<HashSet<(usize, usize)>> {
    if !seen.insert((bb_idx, local, before)) {
        return Some(HashSet::default());
    }

    let bb = BasicBlock::from_usize(bb_idx);
    let data = &bbs[bb];

    // Searching from the end of a block: its terminator is the last place it
    // could define `local`.
    if before.is_none() && data.terminator.as_ref().is_some_and(|t| terminator_writes(t, local)) {
        return None;
    }

    let end = before.unwrap_or(data.statements.len()).min(data.statements.len());
    for (i, stmt) in data.statements[..end].iter().enumerate().rev() {
        match &stmt.kind {
            StatementKind::Assign(b) => {
                let (p, rv) = &**b;
                if p.local != local || p.projection.first() == Some(&ProjectionElem::Deref) {
                    // Another local, or a write *through* the pointer in it.
                    continue;
                }
                if !p.projection.is_empty() {
                    // A partial write into the local itself.
                    return None;
                }
                return match rv {
                    Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, ..), ..) => {
                        Some([(bb_idx, i)].into_iter().collect())
                    }
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) if q.projection.is_empty() => {
                        find_casts(bbs, preds, bb_idx, q.local, Some(i), seen)
                    }
                    _ => None,
                };
            }
            StatementKind::SetDiscriminant { place, .. }
                if place.local == local
                    && place.projection.first() != Some(&ProjectionElem::Deref) =>
            {
                return None;
            }
            _ => {}
        }
    }

    let ps = &preds[bb];
    if ps.is_empty() {
        return None;
    }

    let mut out = HashSet::default();
    for p in ps {
        out.extend(find_casts(bbs, preds, p.index(), local, None, seen)?);
    }

    Some(out)
}

static REWRITE_HITS: AtomicUsize = AtomicUsize::new(0);

pub(super) fn rewrite_monomorphized<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    monomorphized_mir: Body<'tcx>,
) -> Body<'tcx> {
    // Set by cargo-verifopt's own run_cargo_build, on the top-level
    // cargo command it spawns - inherited from there by every
    // downstream process it transitively spawns
    if std::env::var("VERIFOPT_SKIP_REWRITE").is_ok() {
        return monomorphized_mir;
    }

    let hash = tcx.def_path_hash(instance.def_id());
    trace!(
        "[verifopt debug][rewrite_monomorphized entry] instance={:?} def_id={:?} hash={:?} crate={:?}",
        instance,
        instance.def_id(),
        hash,
        tcx.crate_name(instance.def_id().krate),
    );
    let edits = match SHARED_STORE.get_or_init(load_shared_store) {
        Some(shared) => compute_edits(tcx, instance, shared, hash, instance.args, &monomorphized_mir),
        None => return monomorphized_mir,
    };
    if !edits.is_empty() {
        let n = REWRITE_HITS.fetch_add(1, Ordering::Relaxed) + 1;
        debug!(
            "[verifopt debug] hit #{n}: {} edit(s) matched for {:?} (hash {hash:?})",
            edits.len(),
            instance.def_id(),
        );
    }
    apply_edits(tcx, instance, monomorphized_mir, edits)
}
