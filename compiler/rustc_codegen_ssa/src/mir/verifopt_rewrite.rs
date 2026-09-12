use rustc_data_structures::fx::{FxHashSet as HashSet};
use rustc_data_structures::fx::{FxHashMap as HashMap};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::smallvec::SmallVec;
use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BinOp, Body, CastKind, CoercionSource, Const, ConstOperand, Local,
    LocalDecl, Mutability, Operand, Place, ProjectionElem, Rvalue, SourceInfo, Statement,
    StatementKind, SwitchTargets, Terminator, TerminatorKind, UnOp,
};
use rustc_span::def_id::{DefPathHash, LOCAL_CRATE};
use rustc_hir::LangItem;
use rustc_hir::Safety;
use rustc_hir::def::DefKind;
use rustc_middle::mir::pretty::MirWriter;
use rustc_middle::ty;
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{
    AssocKind, FnDef, GenericArg, Instance, List, Ty, TyCtxt, TypingEnv, VtblEntry,
};
use rustc_span::Span;

use std::fs::{File, OpenOptions};
use std::io::Write;

//use std::collections::{HashMap, HashSet};
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::{Deserialize, Serialize};

#[derive(Default)]
pub(super) struct Store {
    pub targets:
        HashMap<(DefPathHash, usize, Vec<DefPathHash>), Vec<(DefPathHash, Option<Vec<DefPathHash>>)>>,
    pub tags: HashMap<
        (DefPathHash, usize, Vec<DefPathHash>),
        Vec<(
            usize,                     /* bb */
            usize,                     /* stmt */
            u64,                       /* tag */
            DefPathHash,               /* impl fn */
            Option<Vec<DefPathHash>>,  /* concrete generic args, when resolvable */
        )>,
    >,
}


#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct SerializableDefPathHash([u8; 16]);

impl From<DefPathHash> for SerializableDefPathHash {
    fn from(dph: DefPathHash) -> Self {
        SerializableDefPathHash(dph.0.to_le_bytes())
    }
}

impl From<SerializableDefPathHash> for DefPathHash {
    fn from(s: SerializableDefPathHash) -> Self {
        DefPathHash(Fingerprint::from_le_bytes(s.0))
    }
}

#[derive(Serialize, Deserialize, Default)]
struct SerializableStore {
    targets: Vec<(
        (SerializableDefPathHash, usize, Vec<SerializableDefPathHash>),
        Vec<(SerializableDefPathHash, Option<Vec<SerializableDefPathHash>>)>,
    )>,
    tags: Vec<(
        (SerializableDefPathHash, usize, Vec<SerializableDefPathHash>),
        Vec<(
            usize,
            usize,
            u64,
            SerializableDefPathHash,
            Option<Vec<SerializableDefPathHash>>,
        )>,
    )>,
}

impl From<&Store> for SerializableStore {
    // Serialization order doesn't affect correctness - the store gets
    // parsed back into an equivalent lookup structure on read, regardless
    // of what order entries appear in the JSON file.
    #[allow(rustc::potential_query_instability)]
    fn from(store: &Store) -> Self {
        let conv_opt_vec = |opt: &Option<Vec<DefPathHash>>| {
            opt.as_ref()
                .map(|v| v.iter().map(|h| SerializableDefPathHash::from(*h)).collect())
        };
        let conv_vec = |v: &Vec<DefPathHash>| -> Vec<SerializableDefPathHash> {
            v.iter().map(|h| SerializableDefPathHash::from(*h)).collect()
        };
        SerializableStore {
            targets: store
                .targets
                .iter()
                .map(|((h, bb, caller_genargs), v)| {
                    (
                        (SerializableDefPathHash::from(*h), *bb, conv_vec(caller_genargs)),
                        v.iter()
                            .map(|(h2, opt)| (SerializableDefPathHash::from(*h2), conv_opt_vec(opt)))
                            .collect(),
                    )
                })
                .collect(),
            tags: store
                .tags
                .iter()
                .map(|((h, bb, caller_genargs), v)| {
                    (
                        (SerializableDefPathHash::from(*h), *bb, conv_vec(caller_genargs)),
                        v.iter()
                            .map(|(bb2, stmt, tag, h2, opt)| {
                                (
                                    *bb2,
                                    *stmt,
                                    *tag,
                                    SerializableDefPathHash::from(*h2),
                                    conv_opt_vec(opt),
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        }
    }
}

impl From<SerializableStore> for Store {
    fn from(s: SerializableStore) -> Self {
        let conv_opt_vec = |opt: Option<Vec<SerializableDefPathHash>>| {
            opt.map(|v| v.into_iter().map(DefPathHash::from).collect())
        };
        let conv_vec =
            |v: Vec<SerializableDefPathHash>| -> Vec<DefPathHash> {
                v.into_iter().map(DefPathHash::from).collect()
            };
        Store {
            targets: s
                .targets
                .into_iter()
                .map(|((h, bb, caller_genargs), v)| {
                    (
                        (DefPathHash::from(h), bb, conv_vec(caller_genargs)),
                        v.into_iter()
                            .map(|(h2, opt)| (DefPathHash::from(h2), conv_opt_vec(opt)))
                            .collect(),
                    )
                })
                .collect(),
            tags: s
                .tags
                .into_iter()
                .map(|((h, bb, caller_genargs), v)| {
                    (
                        (DefPathHash::from(h), bb, conv_vec(caller_genargs)),
                        v.into_iter()
                            .map(|(bb2, stmt, tag, h2, opt)| {
                                (bb2, stmt, tag, DefPathHash::from(h2), conv_opt_vec(opt))
                            })
                            .collect(),
                    )
                })
                .collect(),
        }
    }
}

pub(super) fn dep_rewrite_store_path() -> std::path::PathBuf {
    "verifopt_store.json".into()
}

static SHARED_STORE: OnceLock<Option<Store>> = OnceLock::new();

fn load_shared_store() -> Option<Store> {
    let contents = match std::fs::read_to_string(dep_rewrite_store_path()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!(
                "[verifopt debug] could not read {}: {e}",
                dep_rewrite_store_path().display()
            );
            return None;
        }
    };
    eprintln!(
        "[verifopt debug] read {} bytes from {}",
        contents.len(),
        dep_rewrite_store_path().display()
    );
    let serializable: SerializableStore = match serde_json::from_str(&contents) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "[verifopt debug] failed to deserialize {} into SerializableStore: {e}",
                dep_rewrite_store_path().display()
            );
            return None;
        }
    };
    let store = Store::from(serializable);
    eprintln!(
        "[verifopt debug] loaded store: {} target entries, {} tag entries",
        store.targets.len(),
        store.tags.len()
    );
    Some(store)
}


static DYNAMIC_HITS: AtomicUsize = AtomicUsize::new(0);

static FN_OP_ARGS_MISMATCH: AtomicUsize = AtomicUsize::new(0);
static FN_OP_ARGS_OK: AtomicUsize = AtomicUsize::new(0);

static CRATE_NAME: OnceLock<String> = OnceLock::new();

static MIR_DUMP_FILE: OnceLock<Mutex<File>> = OnceLock::new();

fn mir_dump_file() -> &'static Mutex<File> {
    MIR_DUMP_FILE.get_or_init(|| {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open("mir_dump.txt")
            .expect("failed to open mir_dump.txt for writing");
        Mutex::new(file)
    })
}

fn dump_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, label: &str) {
    let mut buf = Vec::new();

    let writer = MirWriter::new(tcx);
    let _ = writer.write_mir_fn(body, &mut buf);

    let mut file = mir_dump_file().lock().unwrap();
    let _ = writeln!(file, "\n######### MIR {label} #########");
    let _ = file.write_all(&buf);
    let _ = writeln!(file, "######### END {label} #########\n");
}

enum Edit {
    Single(DefPathHash, Option<Vec<DefPathHash>>),
    Pointers(Vec<(DefPathHash, Option<Vec<DefPathHash>>)>),
    Tagged(Vec<(usize, usize, u64, DefPathHash, Option<Vec<DefPathHash>>)>),
}

const MAX_POINTERS_CANDIDATES: usize = 4;

/// Produces a small, fixed, deterministic DefPathHash for a primitive
/// type - not a real DefId hash at all (primitives have no DefId), just
/// a stand-in that lets the existing Vec<DefPathHash> key-component slot
/// also represent primitive generic args (bool, char, ints, floats)
/// without introducing a whole new key-component type and re-touching
/// the serialization layer again.
///
/// Implemented identically on this side and monomorph's own
/// rewrite.rs (see that file's own copy of this same function) - both
/// sides must compute the same sentinel for the same primitive, on the
/// same pinned rustc build, for the store's own keys to ever line up
/// across the two, separate processes at all. A real DefPathHash
/// coinciding with one of these specific, small sentinel values is
/// astronomically unlikely, for the same reason DefPathHash collisions
/// in general are treated as negligible risk elsewhere in this
/// codebase - not a new, additional risk being introduced here.
///
/// FNV-1a, not anything cryptographic or rustc-internal - deliberately
/// simple and self-contained so it's trivial to keep byte-for-byte
/// identical between the two, separate copies of this function.
fn primitive_ty_sentinel(tag: &str) -> DefPathHash {
    fn fnv1a_64(bytes: &[u8]) -> u64 {
        let mut hash: u64 = 0xcbf29ce484222325;
        for &b in bytes {
            hash ^= b as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }
    let h1 = fnv1a_64(tag.as_bytes());
    // Different input for the second half (not just re-hashing h1's own
    // bytes) so a short tag's own two halves don't trivially collide
    // with each other.
    let h2 = fnv1a_64(format!("{tag}#verifopt-sentinel").as_bytes());
    DefPathHash(Fingerprint::new(h1, h2))
}

/// Combines a tag with an ordered list of nested hashes into a single,
/// deterministic sentinel - used for compound types (currently just
/// tuples) whose own identity depends on an ordered set of nested
/// types, each of which may itself already be hashed via hash_ty/
/// primitive_ty_sentinel. Relies on DefPathHash's own Debug output
/// being identical on both this side and monomorph's own copy of this
/// same function, since both operate on the exact same, single
/// rustc-internal DefPathHash type - not something particular to this
/// side alone.
fn combine_hashes(tag: &str, hashes: &[DefPathHash]) -> DefPathHash {
    let joined = hashes.iter().map(|h| format!("{h:?}")).collect::<Vec<_>>().join(",");
    primitive_ty_sentinel(&format!("{tag}:[{joined}]"))
}

/// Recursively hashes a single rustc-internal Ty into a stable,
/// cross-process-comparable DefPathHash, mirroring monomorph's own
/// hash_ty (see that file's own copy of this same function) - handles
/// a concrete, non-generic Adt type via a real DefPathHash, primitive
/// types via the sentinel helper, and tuples by recursively hashing
/// each element and combining. Returns None for anything else (a
/// still-generic type parameter, a reference, a closure, etc.), since
/// there's no stable, cross-process-comparable hash computed for it
/// yet. A top-level function rather than a closure specifically so it
/// can call itself for tuple elements - closures can't recurse by name
/// in Rust.
fn hash_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefPathHash> {
    Some(match ty.kind() {
        ty::Adt(adt_def, sub_genargs) => {
            if !sub_genargs.is_empty() {
                return None;
            }
            tcx.def_path_hash(adt_def.did())
        }
        ty::Bool => primitive_ty_sentinel("prim:bool"),
        ty::Char => primitive_ty_sentinel("prim:char"),
        ty::Int(int_ty) => {
            let tag = match int_ty {
                ty::IntTy::Isize => "prim:isize",
                ty::IntTy::I8 => "prim:i8",
                ty::IntTy::I16 => "prim:i16",
                ty::IntTy::I32 => "prim:i32",
                ty::IntTy::I64 => "prim:i64",
                ty::IntTy::I128 => "prim:i128",
            };
            primitive_ty_sentinel(tag)
        }
        ty::Uint(uint_ty) => {
            let tag = match uint_ty {
                ty::UintTy::Usize => "prim:usize",
                ty::UintTy::U8 => "prim:u8",
                ty::UintTy::U16 => "prim:u16",
                ty::UintTy::U32 => "prim:u32",
                ty::UintTy::U64 => "prim:u64",
                ty::UintTy::U128 => "prim:u128",
            };
            primitive_ty_sentinel(tag)
        }
        ty::Float(float_ty) => {
            let tag = match float_ty {
                ty::FloatTy::F16 => "prim:f16",
                ty::FloatTy::F32 => "prim:f32",
                ty::FloatTy::F64 => "prim:f64",
                ty::FloatTy::F128 => "prim:f128",
            };
            primitive_ty_sentinel(tag)
        }
        ty::Tuple(elems) => {
            let elem_hashes: Option<Vec<DefPathHash>> =
                elems.iter().map(|t| hash_ty(tcx, t)).collect();
            combine_hashes("prim:tuple", &elem_hashes?)
        }
        // Regions/lifetimes are deliberately ignored here (not part of
        // the tag, not hashed) - they're already erased throughout this
        // whole pipeline, and don't affect which concrete
        // devirtualization target applies.
        ty::Ref(_region, inner_ty, mutability) => {
            let tag = match mutability {
                ty::Mutability::Not => "prim:ref:not",
                ty::Mutability::Mut => "prim:ref:mut",
            };
            combine_hashes(tag, &[hash_ty(tcx, *inner_ty)?])
        }
        ty::RawPtr(inner_ty, mutability) => {
            let tag = match mutability {
                ty::Mutability::Not => "prim:rawptr:not",
                ty::Mutability::Mut => "prim:rawptr:mut",
            };
            combine_hashes(tag, &[hash_ty(tcx, *inner_ty)?])
        }
        ty::Slice(inner_ty) => {
            combine_hashes("prim:slice", &[hash_ty(tcx, *inner_ty)?])
        }
        ty::FnPtr(sig_tys, _fn_header) => {
            let fn_sig_tys = sig_tys.skip_binder();
            let elem_hashes: Option<Vec<DefPathHash>> = fn_sig_tys
                .inputs_and_output
                .iter()
                .map(|t| hash_ty(tcx, t))
                .collect();
            combine_hashes("prim:fnptr", &elem_hashes?)
        }
        // Arrays are deliberately not handled yet - unlike everything
        // above, an array's own type also depends on a const-generic
        // length (the "5" in [u32; 5]), which isn't just another Ty to
        // recurse into - extracting a stable, cross-process-comparable
        // hash for an arbitrary const expression is a genuinely
        // different, harder problem than anything handled so far.
        // Closures, dyn types, coroutines, etc. - also not yet handled;
        // returning None here means the caller-genargs use of this
        // function panics rather than silently collapsing distinct
        // instantiations onto the same key.
        _ => return None,
    })
}

/// Mirrors monomorph's own to_genargs_hashes closure (see
/// monomorph/src/rewrite.rs) - delegates the actual per-type hashing to
/// hash_ty above.
///
/// Operates on rustc-internal GenericArgsRef rather than
/// rustc_public::ty::GenericArgs, since this side of the pipeline never
/// goes through rustc_public's own stable-MIR conversion layer at all -
/// unlike monomorph's own copy, which only ever sees the stable type.
fn to_genargs_hashes<'tcx>(
    tcx: TyCtxt<'tcx>,
    genargs: ty::GenericArgsRef<'tcx>,
) -> Option<Vec<DefPathHash>> {
    let mut hashes = Vec::with_capacity(genargs.len());
    for arg in genargs {
        let ty::GenericArgKind::Type(ty) = arg.kind() else {
            return None;
        };
        hashes.push(hash_ty(tcx, ty)?);
    }
    Some(hashes)
}

// The store.targets.keys()/store.tags.keys() check below is order-
// independent (just checks whether any entry matches at all), so
// HashMap iteration order never affects its result - safe to allow,
// same reasoning as the existing #[allow(...)] elsewhere in this file.
#[allow(rustc::potential_query_instability)]
fn compute_edits<'tcx>(
    tcx: TyCtxt<'tcx>,
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

    // Panics rather than silently falling back to a more conservative
    // edit (or skipping this function's own dispatch sites entirely) if
    // the caller's own generic args can't be hashed - see the identical
    // reasoning and panic on monomorph's own side (rewrite.rs). Falling
    // back here would silently reintroduce exactly the span-collision
    // risk this key extension exists to close: different monomorphized
    // instantiations of the same generic function, sharing the same
    // DefPathHash+bb, would fall through to matching store.targets/
    // store.tags entries meant for a *different* instantiation instead
    // of correctly finding nothing at all for this one.
    let Some(caller_genargs_hash) = to_genargs_hashes(tcx, caller_genargs) else {
        panic!(
            "could not hash caller's own generic args for {hash:?} - \
             genargs: {caller_genargs:?} - without this, this dispatch \
             site's own key would collapse different monomorphized \
             instantiations of the same generic function onto the same \
             store entry, silently applying a different instantiation's \
             own rewrite"
        );
    };

    default
        .basic_blocks
        .indices()
        .filter_map(|bb| {
            let key = &(hash, bb.as_usize(), caller_genargs_hash.clone());

            let tags = store.tags.get(key);
            let targets = store.targets.get(key)?;

            if targets.len() == 1 {
                // directly swap terminator
                Some((bb.as_usize(), Edit::Single(targets[0].0, targets[0].1.clone())))
            } else if let Some(tags) = tags {
                // tag dyn casts and switchint
                Some((bb.as_usize(), Edit::Tagged(tags.to_vec())))
            } else if targets.len() > 1 && targets.len() <= MAX_POINTERS_CANDIDATES {
                // direct conditionals on pointers
                Some((bb.as_usize(), Edit::Pointers(targets.to_vec())))
            } else {
                // leave vtable dyn call
                None
            }
        })
        .collect()
}

fn apply_edits<'tcx>(tcx: TyCtxt<'tcx>, default: Body<'tcx>, edits: Vec<(usize, Edit)>) -> Body<'tcx> {
    if edits.is_empty() {
        return default;
    }

    let mut body = default.clone();

    dump_body(tcx, &body, "before");

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
                continue;
            };
            let (defid, gen_args) = match func {
                Operand::Constant(c) => match c.const_.ty().kind() {
                    FnDef(defid, a) => (*defid, *a), // *a: &'tcx List is Copy
                    _ => continue,
                },
                _ => continue,
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

        match edit {
            Edit::Single(hash, self_hash) => {
                let (fnc, self_ty) = match fn_op(tcx, hash, self_hash, gen_args, span) {
                    Ok(v) => v,
                    Err(_) => continue,
                };

                let (recv, new_stmts) = narrow_dyn(
                    tcx,
                    &mut body,
                    source_info,
                    args[0].node.clone(),
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
                }
            }

            Edit::Pointers(hashes) => {
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

                let orig = bbs[bb].terminator().clone();
                let mut fallback = bbs.push(BasicBlockData::new_stmts(vec![], Some(orig), false));
                let n = hashes.len();

                for (i, (hash, self_hash)) in hashes.iter().enumerate() {
                    let (fnc, self_ty) = match fn_op(tcx, *hash, self_hash.clone(), gen_args, span)
                    {
                        Ok(v) => v,
                        Err(_) => continue,
                    };

                    let (recv, new_stmts) = narrow_dyn(
                        tcx,
                        &mut body,
                        source_info,
                        args[0].node.clone(),
                        self_ty,
                        span,
                    );
                    let mut new_args = args.clone();
                    new_args[0].node = Operand::Move(recv);

                    let call_bb = bbs.push(BasicBlockData::new_stmts(
                        new_stmts,
                        Some(Terminator {
                            source_info,
                            kind: TerminatorKind::Call {
                                func: fnc.clone(),
                                args: new_args,
                                destination: dest,
                                target: target,
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
            }

            Edit::Tagged(sites) => {
                let recv_local = match &args[0].node {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
                    _ => continue,
                };

                let preds = default.basic_blocks.predecessors();

                let found = find_casts(&bbs, preds, bb_idx, recv_local, &mut HashSet::default());

                let planned: HashSet<(usize, usize)> = sites
                    .iter()
                    .map(|(bb, stmt, _, _, _)| (*bb, *stmt))
                    .collect();
                if found != Some(planned) {
                    continue;
                }

                let tag_local = body.local_decls.push(LocalDecl::new(tcx.types.usize, span));

                for (bb_idx, stmt_idx, tag, _, _) in &sites {
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

                let orig = bbs[bb].terminator().clone();
                let fallback = bbs.push(BasicBlockData::new_stmts(vec![], Some(orig), false));

                let mut arms = Vec::new();

                for (_, _, tag, impl_hash, self_hash) in &sites {
                    let (fnc, self_ty) =
                        match fn_op(tcx, *impl_hash, self_hash.clone(), gen_args, span) {
                            Ok(v) => v,
                            Err(_) => continue,
                        };
                    let (recv, stmts) = narrow_dyn(
                        tcx,
                        &mut body,
                        source_info,
                        args[0].node.clone(),
                        self_ty,
                        span,
                    );

                    let mut new_args = args.clone();
                    new_args[0].node = Operand::Move(recv);

                    let cb = bbs.push(BasicBlockData::new_stmts(
                        stmts,
                        Some(Terminator {
                            source_info,
                            kind: TerminatorKind::Call {
                                func: fnc,
                                args: new_args,
                                destination: dest,
                                target,
                                unwind,
                                call_source,
                                fn_span: span,
                            },
                        }),
                        false,
                    ));
                    arms.push((*tag as u128, cb));
                }

                bbs[bb].terminator = Some(Terminator {
                    source_info,
                    kind: TerminatorKind::SwitchInt {
                        discr: Operand::Copy(Place::from(tag_local)),
                        targets: SwitchTargets::new(arms.into_iter(), fallback),
                    },
                });
            }
        }
    }

    *body.basic_blocks_mut() = bbs;

    dump_body(tcx, &body, "after");

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
fn safe_def_path_hash_to_def_id(tcx: TyCtxt<'_>, hash: DefPathHash) -> Option<rustc_span::def_id::DefId> {
    if !tcx.untracked().stable_crate_ids.read().contains_key(&hash.stable_crate_id()) {
        return None;
    }
    tcx.def_path_hash_to_def_id(hash)
}

fn fn_op<'tcx>(
    tcx: TyCtxt<'tcx>,
    hash: DefPathHash,
    self_hashes: Option<Vec<DefPathHash>>,
    gen_args: &'tcx List<GenericArg<'tcx>>,
    span: Span,
) -> Result<(Operand<'tcx>, Ty<'tcx>), ()> {
    let target_did = safe_def_path_hash_to_def_id(tcx, hash).ok_or(())?;

    let args = match &self_hashes {
        Some(hashes) => {
            let tys: Vec<Ty<'tcx>> = hashes
                .iter()
                .map(|h| {
                    let did = safe_def_path_hash_to_def_id(tcx, *h).ok_or(())?;
                    Ok(tcx.type_of(did).instantiate_identity())
                })
                .collect::<Result<Vec<_>, ()>>()?;
            let arg_list: Vec<GenericArg<'tcx>> = tys.into_iter().map(|t| t.into()).collect();
            tcx.mk_args(&arg_list)
        }
        None => tcx.mk_args_from_iter(gen_args.iter().skip(1)),
    };

    let _ = CRATE_NAME.get_or_init(|| tcx.crate_name(LOCAL_CRATE).to_string());
    if args.len() != tcx.generics_of(target_did).count() {
        FN_OP_ARGS_MISMATCH.fetch_add(1, Ordering::Relaxed);
        return Err(());
    }
    FN_OP_ARGS_OK.fetch_add(1, Ordering::Relaxed);

    let instance =
        match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), target_did, args) {
            Ok(Some(inst)) => inst,
            _ => return Err(()),
        };

    let fn_ty = instance.ty(tcx, TypingEnv::fully_monomorphized());
    let new_const = Const::zero_sized(fn_ty);

    let op = Operand::Constant(Box::new(ConstOperand {
        span: span,
        user_ty: None,
        const_: new_const,
    }));

    let parent_did = tcx.parent(target_did);
    let raw_self_ty = if tcx.def_kind(parent_did) == DefKind::Trait {
        match &self_hashes {
            Some(hashes) if !hashes.is_empty() => {
                let self_did = safe_def_path_hash_to_def_id(tcx, hashes[0]).ok_or(())?;
                tcx.type_of(self_did).instantiate_identity()
            }
            _ => return Err(()),
        }
    } else {
        tcx.type_of(parent_did).instantiate(tcx, instance.args)
    };
    let self_ty = match tcx.try_normalize_erasing_regions(TypingEnv::fully_monomorphized(), raw_self_ty)
    {
        Ok(ty) => ty,
        Err(_) => return Err(()),
    };

    Ok((op, self_ty))
}

fn narrow_dyn<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    si: SourceInfo,
    recv: Operand<'tcx>,
    self_ty: Ty<'tcx>,
    span: Span,
) -> (Place<'tcx>, Vec<Statement<'tcx>>) {
    let ptr_ty = Ty::new_ptr(tcx, self_ty, Mutability::Not);
    let ref_ty = Ty::new_ref(tcx, tcx.lifetimes.re_erased, self_ty, Mutability::Not);

    let mut stmts = Vec::new();

    let thin = Place::from(body.local_decls.push(LocalDecl::new(ptr_ty, span)));
    stmts.push(Statement::new(
        si,
        StatementKind::Assign(Box::new((
            thin,
            Rvalue::Cast(CastKind::PtrToPtr, recv, ptr_ty),
        ))),
    ));

    let deref = Place {
        local: thin.local,
        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
    };

    let out = Place::from(body.local_decls.push(LocalDecl::new(ref_ty, span)));
    stmts.push(Statement::new(
        si,
        StatementKind::Assign(Box::new((
            out,
            Rvalue::Ref(
                tcx.lifetimes.re_erased,
                rustc_middle::mir::BorrowKind::Shared,
                deref,
            ),
        ))),
    ));

    (out, stmts)
}

// The only thing done with this result is a set-equality check, which only
// depends on set membership - completely unaffected by iteration or insertion order.
#[allow(rustc::potential_query_instability)]
fn find_casts<'tcx>(
    bbs: &IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    preds: &IndexVec<BasicBlock, SmallVec<[BasicBlock; 4]>>,
    bb_idx: usize,
    local: Local,
    seen: &mut HashSet<(usize, Local)>,
) -> Option<HashSet<(usize, usize)>> {
    if !seen.insert((bb_idx, local)) {
        return Some(HashSet::default());
    }

    let bb = BasicBlock::from_usize(bb_idx);

    for (i, stmt) in bbs[bb].statements.iter().enumerate().rev() {
        let StatementKind::Assign(b) = &stmt.kind else {
            continue;
        };
        let (p, rv) = *b.clone();
        if p.local != local || !p.projection.is_empty() {
            continue;
        }

        return match rv {
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, ..), ..) => {
                Some([(bb_idx, i)].into_iter().collect())
            }
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) if q.projection.is_empty() => {
                find_casts(bbs, preds, bb_idx, q.local, seen)
            }
            _ => None,
        };
    }

    let ps = &preds[bb];
    if ps.is_empty() {
        return None;
    }

    let mut out = HashSet::default();
    for p in ps {
        out.extend(find_casts(bbs, preds, p.index(), local, seen)?);
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
    let edits = match SHARED_STORE.get_or_init(load_shared_store) {
        Some(shared) => compute_edits(tcx, shared, hash, instance.args, &monomorphized_mir),
        None => return monomorphized_mir,
    };
    if !edits.is_empty() {
        let n = REWRITE_HITS.fetch_add(1, Ordering::Relaxed) + 1;
        eprintln!(
            "[verifopt debug] hit #{n}: {} edit(s) matched for {:?} (hash {hash:?})",
            edits.len(),
            instance.def_id(),
        );
    }
    apply_edits(tcx, monomorphized_mir, edits)
}
