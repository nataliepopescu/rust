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
    AssocKind, FnDef, GenericArg, Instance, InstanceKind, List, Ty, TyCtxt, TypingEnv, VtblEntry,
};
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_span::def_id::DefId;
use rustc_span::Span;

use std::fs::{File, OpenOptions};
use std::io::Write;

//use std::collections::{HashMap, HashSet};
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::{Deserialize, Serialize};

use tracing::debug;

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
    /// Every sentinel hash (see primitive_ty_sentinel/combine_hashes)
    /// this store's own targets/tags entries reference, paired with the
    /// shape it was computed from - see TyShape's own doc comment for
    /// why this is needed at all. Carries discovery's own
    /// SHAPE_REGISTRY across the process boundary (see
    /// load_shared_store) into a later, separate rewrite-application
    /// process that may never independently rehash the same type.
    pub shapes: HashMap<DefPathHash, TyShape>,
}


#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) struct SerializableDefPathHash([u8; 16]);

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
    #[serde(default)]
    shapes: Vec<(SerializableDefPathHash, TyShape)>,
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
            shapes: store
                .shapes
                .iter()
                .map(|(h, shape)| (SerializableDefPathHash::from(*h), shape.clone()))
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
            shapes: s
                .shapes
                .into_iter()
                .map(|(h, shape)| (DefPathHash::from(h), shape))
                .collect(),
        }
    }
}

pub(super) fn dep_rewrite_store_path() -> std::path::PathBuf {
    match std::env::var_os("VERIFOPT_STORE_DIR") {
        Some(dir) => std::path::PathBuf::from(dir).join("verifopt_store.json"),
        None => "verifopt_store.json".into(),
    }
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
    let serializable: SerializableStore = match serde_json::from_str(&contents) {
        Ok(s) => s,
        Err(e) => {
            debug!(
                "[verifopt debug] failed to deserialize {} into SerializableStore: {e}",
                dep_rewrite_store_path().display()
            );
            return None;
        }
    };
    let store = Store::from(serializable);
    debug!(
        "[verifopt debug] loaded store: {} target entries, {} tag entries, {} shape entries",
        store.targets.len(),
        store.tags.len(),
        store.shapes.len()
    );
    // Seed the shape registry from the store's own shapes, read off disk -
    // this is what lets ty_from_shape (see fn_op) resolve a sentinel hash
    // this process never independently computed itself, e.g. one only
    // ever hashed during discovery's own, separate, earlier run.
    {
        let mut registry = shape_registry().lock().unwrap();
        // Iteration order genuinely doesn't matter here - each entry is
        // independently inserted into a separate map, so any order
        // produces the same final result.
        #[allow(rustc::potential_query_instability)]
        for (hash, shape) in &store.shapes {
            registry.entry(*hash).or_insert_with(|| shape.clone());
        }
    }
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

static EDIT_KIND_STATS_FILE: OnceLock<Mutex<File>> = OnceLock::new();

fn edit_kind_stats_file() -> &'static Mutex<File> {
    EDIT_KIND_STATS_FILE.get_or_init(|| {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open("verifopt_edit_kind_stats.txt")
            .expect("failed to open verifopt_edit_kind_stats.txt for writing");
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
    let _ = writeln!(file, "{kind}");
}

fn dump_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, label: &str) {
    let mut buf = Vec::new();

    let writer = MirWriter::new(tcx);
    let _ = ty::print::with_no_trimmed_paths!(writer.write_mir_fn(body, &mut buf));

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
/// A serializable description of a type's own structure, for types
/// hashed via a sentinel (primitive_ty_sentinel/combine_hashes) rather
/// than a real DefPathHash - a sentinel is a one-way FNV hash with no
/// actual DefId behind it at all, so there's no way to recover the
/// original type from the hash alone. This carries enough structure to
/// rebuild an equivalent Ty within any TyCtxt, once paired with its own
/// sentinel hash in a lookup table (see SHAPE_REGISTRY below and
/// Store's own `shapes` field) - mirrors hash_ty's own match arms as
/// data, one variant per shape hash_ty already knows how to hash.
/// ADT is deliberately absent - a nominal type's own DefPathHash is
/// already a real DefId hash, already resolvable via
/// safe_def_path_hash_to_def_id with no shape data needed at all.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(super) enum TyShape {
    Primitive(String),
    Tuple(Vec<TyShape>),
    Ref(bool /* mutable */, Box<TyShape>),
    RawPtr(bool /* mutable */, Box<TyShape>),
    Slice(Box<TyShape>),
    FnPtr {
        inputs_and_output: Vec<TyShape>,
        abi: String,
        safe: bool,
        c_variadic: bool,
    },
    Dyn(SerializableDefPathHash /* trait DefId hash */, Vec<TyShape>),
}

/// Sentinel hash -> the shape it was computed from, populated as a side
/// effect every time hash_ty computes a sentinel-based hash (see the
/// record_shape calls added to hash_ty's own match arms below).
/// Consulted by ty_from_shape (see below fn_op) once
/// safe_def_path_hash_to_def_id already failed to resolve a hash to a
/// real DefId - which is always the case for a sentinel, since it was
/// never a real DefId hash to begin with. Populated fresh within
/// whichever single rustc process is currently running (see
/// load_shared_store, which seeds this from the store's own `shapes`
/// field read off disk, carrying discovery's own shapes across the
/// process boundary into a later, separate rewrite-application
/// process that never independently rehashes the same type at all).
static SHAPE_REGISTRY: OnceLock<Mutex<HashMap<DefPathHash, TyShape>>> = OnceLock::new();

fn shape_registry() -> &'static Mutex<HashMap<DefPathHash, TyShape>> {
    SHAPE_REGISTRY.get_or_init(|| Mutex::new(HashMap::default()))
}

fn record_shape(hash: DefPathHash, shape: TyShape) -> DefPathHash {
    shape_registry().lock().unwrap().insert(hash, shape);
    hash
}

/// Rebuilds a genuine Ty<'tcx> from a TyShape, within the current tcx -
/// the reverse of hash_ty, for shapes that were never a real DefId hash
/// at all. Mirrors hash_ty's own match arms, one direction each.
fn ty_from_shape<'tcx>(tcx: TyCtxt<'tcx>, shape: &TyShape) -> Option<Ty<'tcx>> {
    Some(match shape {
        TyShape::Primitive(tag) => match tag.as_str() {
            "prim:bool" => tcx.types.bool,
            "prim:char" => tcx.types.char,
            "prim:isize" => tcx.types.isize,
            "prim:i8" => tcx.types.i8,
            "prim:i16" => tcx.types.i16,
            "prim:i32" => tcx.types.i32,
            "prim:i64" => tcx.types.i64,
            "prim:i128" => tcx.types.i128,
            "prim:usize" => tcx.types.usize,
            "prim:u8" => tcx.types.u8,
            "prim:u16" => tcx.types.u16,
            "prim:u32" => tcx.types.u32,
            "prim:u64" => tcx.types.u64,
            "prim:u128" => tcx.types.u128,
            "prim:f16" => tcx.types.f16,
            "prim:f32" => tcx.types.f32,
            "prim:f64" => tcx.types.f64,
            "prim:f128" => tcx.types.f128,
            _ => return None,
        },
        TyShape::Tuple(elems) => {
            let tys: Vec<Ty<'tcx>> =
                elems.iter().map(|e| ty_from_shape(tcx, e)).collect::<Option<_>>()?;
            Ty::new_tup(tcx, &tys)
        }
        TyShape::Ref(mutable, inner) => {
            let inner_ty = ty_from_shape(tcx, inner)?;
            let mutability = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ref(tcx, tcx.lifetimes.re_erased, inner_ty, mutability)
        }
        TyShape::RawPtr(mutable, inner) => {
            let inner_ty = ty_from_shape(tcx, inner)?;
            let mutability = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ptr(tcx, inner_ty, mutability)
        }
        TyShape::Slice(inner) => {
            let inner_ty = ty_from_shape(tcx, inner)?;
            Ty::new_slice(tcx, inner_ty)
        }
        TyShape::FnPtr { inputs_and_output, abi, safe, c_variadic } => {
            let tys: Vec<Ty<'tcx>> = inputs_and_output
                .iter()
                .map(|e| ty_from_shape(tcx, e))
                .collect::<Option<_>>()?;
            let parsed_abi = abi.parse::<rustc_abi::ExternAbi>().ok()?;
            let sig = ty::FnSig {
                inputs_and_output: tcx.mk_type_list_from_iter(tys.iter().copied()),
                c_variadic: *c_variadic,
                safety: if *safe { rustc_hir::Safety::Safe } else { rustc_hir::Safety::Unsafe },
                abi: parsed_abi,
            };
            Ty::new_fn_ptr(tcx, ty::Binder::dummy(sig))
        }
        TyShape::Dyn(trait_hash, genarg_shapes) => {
            let trait_did = safe_def_path_hash_to_def_id(tcx, DefPathHash::from(*trait_hash))?;
            let genarg_tys: Vec<Ty<'tcx>> =
                genarg_shapes.iter().map(|s| ty_from_shape(tcx, s)).collect::<Option<_>>()?;
            let trait_ref = ty::TraitRef::new(tcx, trait_did, genarg_tys);
            let predicate = ty::Binder::dummy(ty::ExistentialPredicate::Trait(
                ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref),
            ));
            let predicates = tcx.mk_poly_existential_predicates(&[predicate]);
            Ty::new_dynamic(tcx, predicates, tcx.lifetimes.re_erased)
        }
    })
}

/// Mirrors hash_ty's own match arms exactly, but produces the TyShape
/// a given hash was computed from, rather than the hash itself. Called
/// only at the top level (see to_genargs_hashes below), not
/// recursively alongside every nested hash_ty call - a TyShape already
/// embeds its own nested structure directly, so there's no need for a
/// separate registry entry per sub-component.
fn ty_to_shape<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TyShape> {
    Some(match ty.kind() {
        ty::Adt(..) => return None,
        ty::Bool => TyShape::Primitive("prim:bool".to_string()),
        ty::Char => TyShape::Primitive("prim:char".to_string()),
        ty::Int(int_ty) => {
            let tag = match int_ty {
                ty::IntTy::Isize => "prim:isize",
                ty::IntTy::I8 => "prim:i8",
                ty::IntTy::I16 => "prim:i16",
                ty::IntTy::I32 => "prim:i32",
                ty::IntTy::I64 => "prim:i64",
                ty::IntTy::I128 => "prim:i128",
            };
            TyShape::Primitive(tag.to_string())
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
            TyShape::Primitive(tag.to_string())
        }
        ty::Float(float_ty) => {
            let tag = match float_ty {
                ty::FloatTy::F16 => "prim:f16",
                ty::FloatTy::F32 => "prim:f32",
                ty::FloatTy::F64 => "prim:f64",
                ty::FloatTy::F128 => "prim:f128",
            };
            TyShape::Primitive(tag.to_string())
        }
        ty::Tuple(elems) => {
            let shapes: Option<Vec<TyShape>> =
                elems.iter().map(|t| ty_to_shape(tcx, t)).collect();
            TyShape::Tuple(shapes?)
        }
        ty::Ref(_region, inner_ty, mutability) => {
            TyShape::Ref(*mutability == ty::Mutability::Mut, Box::new(ty_to_shape(tcx, *inner_ty)?))
        }
        ty::RawPtr(inner_ty, mutability) => TyShape::RawPtr(
            *mutability == ty::Mutability::Mut,
            Box::new(ty_to_shape(tcx, *inner_ty)?),
        ),
        ty::Slice(inner_ty) => TyShape::Slice(Box::new(ty_to_shape(tcx, *inner_ty)?)),
        ty::FnPtr(sig_tys, fn_header) => {
            let fn_sig_tys = sig_tys.skip_binder();
            let shapes: Option<Vec<TyShape>> =
                fn_sig_tys.inputs_and_output.iter().map(|t| ty_to_shape(tcx, t)).collect();
            TyShape::FnPtr {
                inputs_and_output: shapes?,
                abi: fn_header.abi.name().to_string(),
                safe: fn_header.safety.is_safe(),
                c_variadic: fn_header.c_variadic,
            }
        }
        ty::Dynamic(predicates, _region) => {
            let [binder] = predicates.as_slice() else {
                return None;
            };
            let ty::ExistentialPredicate::Trait(trait_ref) = binder.skip_binder() else {
                return None;
            };
            let trait_hash = SerializableDefPathHash::from(tcx.def_path_hash(trait_ref.def_id));
            let genarg_shapes: Option<Vec<TyShape>> = trait_ref
                .args
                .into_iter()
                .map(|arg| {
                    let ty::GenericArgKind::Type(t) = arg.kind() else {
                        return None;
                    };
                    ty_to_shape(tcx, t)
                })
                .collect();
            TyShape::Dyn(trait_hash, genarg_shapes?)
        }
        _ => return None,
    })
}

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
        ty::FnPtr(sig_tys, fn_header) => {
            let fn_sig_tys = sig_tys.skip_binder();
            let mut elem_hashes: Vec<DefPathHash> = fn_sig_tys
                .inputs_and_output
                .iter()
                .map(|t| hash_ty(tcx, t))
                .collect::<Option<_>>()?;
            let header_tag = format!(
                "prim:fnptr:header:{}:{}:{}",
                fn_header.abi.name(),
                fn_header.safety.is_safe(),
                fn_header.c_variadic,
            );
            elem_hashes.push(primitive_ty_sentinel(&header_tag));
            combine_hashes("prim:fnptr", &elem_hashes)
        }
        // Only the common case is handled: exactly one predicate, and
        // that predicate is a plain trait bound (Send/Sync-style
        // auto-traits, or an associated-type binding like
        // `dyn Iterator<Item = u32>`, both return None here - not yet
        // handled, same as everything else this comment block already
        // covers).
        ty::Dynamic(predicates, _region) => {
            let [binder] = predicates.as_slice() else {
                return None;
            };
            let ty::ExistentialPredicate::Trait(trait_ref) = binder.skip_binder() else {
                return None;
            };
            let trait_hash = tcx.def_path_hash(trait_ref.def_id);
            let genarg_hashes: Option<Vec<DefPathHash>> = trait_ref
                .args
                .into_iter()
                .map(|arg| {
                    let ty::GenericArgKind::Type(t) = arg.kind() else {
                        return None;
                    };
                    hash_ty(tcx, t)
                })
                .collect();
            let mut all_hashes = vec![trait_hash];
            all_hashes.extend(genarg_hashes?);
            combine_hashes("prim:dyn", &all_hashes)
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
        let hash = hash_ty(tcx, ty)?;
        if let Some(shape) = ty_to_shape(tcx, ty) {
            record_shape(hash, shape);
        }
        hashes.push(hash);
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

        // Decide up front whether the receiver can be narrowed at all, so an
        // unsupported receiver bails out before any statements are emitted.
        let recv_ty = args[0].node.ty(&local_decls, tcx);
        let Some(recv_kind) = RecvKind::of(recv_ty) else {
            debug!("[verifopt debug][apply_edits] skipping bb {:?}: unsupported receiver type {:?}", bb, recv_ty);
            continue;
        };

        match edit {
            Edit::Single(hash, self_hash) => {
                let (fnc, self_ty) = match fn_op(tcx, defid, hash, self_hash, gen_args, span) {
                    Ok(v) => v,
                    Err(_) => continue,
                };

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
                    log_edit_kind("single");
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
                    let (fnc, self_ty) = match fn_op(tcx, defid, *hash, self_hash.clone(), gen_args, span)
                    {
                        Ok(v) => v,
                        Err(_) => continue,
                    };

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
                log_edit_kind("pointers");
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
                log_edit_kind("tagged");
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
    // The DefId of the original (virtual) callee, e.g. FnMut::call_mut.
    // Needed for closure-like targets, whose DefId is not callable itself.
    orig_callee: DefId,
    hash: DefPathHash,
    self_hashes: Option<Vec<DefPathHash>>,
    gen_args: &'tcx List<GenericArg<'tcx>>,
    span: Span,
) -> Result<(Operand<'tcx>, Ty<'tcx>), ()> {
    let target_did = match safe_def_path_hash_to_def_id(tcx, hash) {
        Some(did) => did,
        None => {
            debug!("[verifopt debug][fn_op] FAILED at target_did resolution, hash={:?}", hash);
            return Err(());
        }
    };

    let args = match &self_hashes {
        Some(hashes) => {
            let tys: Vec<Ty<'tcx>> = match hashes
                .iter()
                .map(|h| {
                    if let Some(did) = safe_def_path_hash_to_def_id(tcx, *h) {
                        return Ok(tcx.type_of(did).instantiate_identity());
                    }
                    // Not a real DefId hash at all - safe_def_path_hash_to_def_id
                    // can never resolve one of these (see TyShape's own doc
                    // comment). Rebuild it directly from its own recorded
                    // shape instead, if this process has one - either because
                    // it hashed this same type itself, or because it read the
                    // shape in from the store (see load_shared_store).
                    let shape = shape_registry().lock().unwrap().get(h).cloned();
                    match shape.and_then(|s| ty_from_shape(tcx, &s)) {
                        Some(ty) => Ok(ty),
                        None => Err(()),
                    }
                })
                .collect::<Result<Vec<_>, ()>>()
            {
                Ok(v) => v,
                Err(_) => {
                    debug!("[verifopt debug][fn_op] FAILED at self_hashes -> tys resolution, target_did={:?} self_hashes={:?}", target_did, self_hashes);
                    return Err(());
                }
            };
            let arg_list: Vec<GenericArg<'tcx>> = tys.into_iter().map(|t| t.into()).collect();
            tcx.mk_args(&arg_list)
        }
        None => tcx.mk_args_from_iter(gen_args.iter().skip(1)),
    };

    let _ = CRATE_NAME.get_or_init(|| tcx.crate_name(LOCAL_CRATE).to_string());
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

    let instance =
        match Instance::try_resolve(tcx, TypingEnv::fully_monomorphized(), target_did, args) {
            Ok(Some(inst)) => inst,
            other => {
                debug!("[verifopt debug][fn_op] FAILED at Instance::try_resolve: target_did={:?} args={:?} result={:?}", target_did, args, other);
                return Err(());
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
                    if let Some(did) = safe_def_path_hash_to_def_id(tcx, hashes[0]) {
                        tcx.type_of(did).instantiate_identity()
                    } else {
                        let shape = shape_registry().lock().unwrap().get(&hashes[0]).cloned();
                        match shape.and_then(|s| ty_from_shape(tcx, &s)) {
                            Some(ty) => ty,
                            None => {
                                debug!("[verifopt debug][fn_op] FAILED at self_did resolution (trait parent branch): target_did={:?} self_hashes={:?}", target_did, self_hashes);
                                return Err(());
                            }
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
    debug!(
        "[verifopt debug][rewrite_monomorphized entry] instance={:?} def_id={:?} hash={:?} crate={:?}",
        instance,
        instance.def_id(),
        hash,
        tcx.crate_name(instance.def_id().krate),
    );
    let edits = match SHARED_STORE.get_or_init(load_shared_store) {
        Some(shared) => compute_edits(tcx, shared, hash, instance.args, &monomorphized_mir),
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
    apply_edits(tcx, monomorphized_mir, edits)
}
