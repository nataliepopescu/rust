//! Serializable type shapes: enough structure to rebuild a type from a
//! sentinel hash on the reading side (sentinels are one-way).

use std::sync::{Mutex, MutexGuard, OnceLock};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::{CtorKind, CtorOf, DefKind};
use rustc_middle::ty::{self, GenericArg, GenericArgKind, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::{DefId, DefPathHash};
use serde::{Deserialize, Serialize};

use crate::hash::{const_scalar, lifetime_arg_hash, prim_tag};

/// A `DefPathHash` in a serde-friendly form (little-endian bytes).
#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct HashBytes(pub [u8; 16]);

impl From<DefPathHash> for HashBytes {
    fn from(h: DefPathHash) -> Self {
        HashBytes(h.0.to_le_bytes())
    }
}

impl From<HashBytes> for DefPathHash {
    fn from(b: HashBytes) -> Self {
        DefPathHash(Fingerprint::from_le_bytes(b.0))
    }
}

/// Structure of a hashed type. Mirrors [`crate::hash_ty`]'s cases.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub enum TyShape {
    Primitive(String),
    /// A (possibly generic) ADT: its own DefPathHash plus its args.
    Adt(HashBytes, Vec<ArgShape>),
    Tuple(Vec<TyShape>),
    /// `&'r T`: mutability, pointee, and the region (erased, or bound by
    /// an enclosing binder).
    Ref(bool /* mutable */, Box<TyShape>, Box<ArgShape>),
    RawPtr(bool /* mutable */, Box<TyShape>),
    Slice(Box<TyShape>),
    Array(Box<TyShape>, u64),
    /// `bound_regions` is the number of (anonymous) late-bound regions the
    /// signature's binder introduces: `for<'a> fn(&'a u8)` has one.
    FnPtr {
        inputs_and_output: Vec<TyShape>,
        abi: String,
        safe: bool,
        c_variadic: bool,
        bound_regions: u32,
    },
    /// `dyn ...`: every existential predicate in rustc's canonical order,
    /// each with its binder's bound-region count, plus the object lifetime.
    Dyn(Vec<(u32, PredShape)>, Box<ArgShape>),
    /// Nominal non-ADT types: DefPathHash plus the item's own args.
    Closure(HashBytes, Vec<ArgShape>),
    Coroutine(HashBytes, Vec<ArgShape>),
    CoroutineClosure(HashBytes, Vec<ArgShape>),
    FnDef(HashBytes, Vec<ArgShape>),
    Foreign(HashBytes),
}

/// One existential predicate of a `dyn` type.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub enum PredShape {
    /// Principal trait: DefPathHash + non-Self args.
    Trait(HashBytes, Vec<ArgShape>),
    /// `Item = X`: associated item's DefPathHash + its non-Self args + term.
    Projection(HashBytes, Vec<ArgShape>, Box<ArgShape>),
    /// `+ Send` etc.
    AutoTrait(HashBytes),
}

/// Structure of one generic argument.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub enum ArgShape {
    /// A free or erased region; always rebuilt as an erased region.
    Lifetime,
    /// A region bound by an enclosing binder, by (De Bruijn index, var).
    /// Codegen-side types have their bound regions anonymized, so these are
    /// always rebuilt as anonymous.
    BoundRegion { debruijn: u32, var: u32 },
    Type(TyShape),
    /// A scalar const: its type plus raw bits (as a decimal string, since
    /// u128 isn't reliably round-tripped through JSON numbers).
    Const { ty: TyShape, bits: String },
}

pub fn ty_to_shape<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TyShape> {
    if let Some(tag) = prim_tag(ty) {
        return Some(TyShape::Primitive(tag.to_string()));
    }
    Some(match ty.kind() {
        ty::Adt(adt_def, args) => TyShape::Adt(
            HashBytes::from(tcx.def_path_hash(adt_def.did())),
            args.iter().map(|a| arg_to_shape(tcx, a)).collect::<Option<_>>()?,
        ),
        ty::Tuple(elems) => {
            TyShape::Tuple(elems.iter().map(|t| ty_to_shape(tcx, t)).collect::<Option<_>>()?)
        }
        ty::Ref(region, inner, mutability) => TyShape::Ref(
            mutability.is_mut(),
            Box::new(ty_to_shape(tcx, *inner)?),
            Box::new(region_to_shape(*region)?),
        ),
        ty::RawPtr(inner, mutability) => {
            TyShape::RawPtr(mutability.is_mut(), Box::new(ty_to_shape(tcx, *inner)?))
        }
        ty::Slice(inner) => TyShape::Slice(Box::new(ty_to_shape(tcx, *inner)?)),
        ty::Array(elem, len) => {
            TyShape::Array(Box::new(ty_to_shape(tcx, *elem)?), len.try_to_target_usize(tcx)?)
        }
        ty::FnPtr(sig_tys, fn_header) => TyShape::FnPtr {
            bound_regions: region_binder_len(sig_tys.bound_vars())?,
            inputs_and_output: sig_tys
                .skip_binder()
                .inputs_and_output
                .iter()
                .map(|t| ty_to_shape(tcx, t))
                .collect::<Option<_>>()?,
            abi: fn_header.abi.name().to_string(),
            safe: fn_header.safety.is_safe(),
            c_variadic: fn_header.c_variadic,
        },
        ty::Dynamic(predicates, region) => {
            let mut preds = Vec::with_capacity(predicates.len());
            for binder in predicates.iter() {
                let bound_regions = region_binder_len(binder.bound_vars())?;
                preds.push((bound_regions, match binder.skip_binder() {
                    ty::ExistentialPredicate::Trait(trait_ref) => PredShape::Trait(
                        HashBytes::from(tcx.def_path_hash(trait_ref.def_id)),
                        trait_ref.args.iter().map(|a| arg_to_shape(tcx, a)).collect::<Option<_>>()?,
                    ),
                    ty::ExistentialPredicate::Projection(proj) => PredShape::Projection(
                        HashBytes::from(tcx.def_path_hash(proj.def_id)),
                        proj.args.iter().map(|a| arg_to_shape(tcx, a)).collect::<Option<_>>()?,
                        Box::new(match proj.term.kind() {
                            ty::TermKind::Ty(t) => ArgShape::Type(ty_to_shape(tcx, t)?),
                            ty::TermKind::Const(ct) => arg_to_shape(tcx, ct.into())?,
                        }),
                    ),
                    ty::ExistentialPredicate::AutoTrait(did) => {
                        PredShape::AutoTrait(HashBytes::from(tcx.def_path_hash(did)))
                    }
                }));
            }
            TyShape::Dyn(preds, Box::new(region_to_shape(*region)?))
        }
        ty::Closure(did, args) => TyShape::Closure(item_hash(tcx, *did), args_to_shapes(tcx, args)?),
        ty::Coroutine(did, args) => {
            TyShape::Coroutine(item_hash(tcx, *did), args_to_shapes(tcx, args)?)
        }
        ty::CoroutineClosure(did, args) => {
            TyShape::CoroutineClosure(item_hash(tcx, *did), args_to_shapes(tcx, args)?)
        }
        ty::FnDef(did, args) => TyShape::FnDef(item_hash(tcx, *did), args_to_shapes(tcx, args)?),
        ty::Foreign(did) => TyShape::Foreign(item_hash(tcx, *did)),
        _ => return None,
    })
}

fn region_to_shape(r: ty::Region<'_>) -> Option<ArgShape> {
    match r.kind() {
        ty::ReBound(ty::BoundVarIndexKind::Bound(debruijn), br) => {
            Some(ArgShape::BoundRegion { debruijn: debruijn.as_u32(), var: br.var.as_u32() })
        }
        // Canonical bound vars only exist inside the trait solver.
        ty::ReBound(ty::BoundVarIndexKind::Canonical, _) => None,
        _ => Some(ArgShape::Lifetime),
    }
}

/// Number of vars a binder introduces, if they're all regions (binders over
/// types or consts - the unstable non_lifetime_binders - aren't supported).
fn region_binder_len(vars: &ty::List<ty::BoundVariableKind>) -> Option<u32> {
    vars.iter()
        .all(|v| matches!(v, ty::BoundVariableKind::Region(_)))
        .then(|| u32::try_from(vars.len()).ok())
        .flatten()
}

fn anon_region_vars<'tcx>(tcx: TyCtxt<'tcx>, n: u32) -> &'tcx ty::List<ty::BoundVariableKind> {
    let kinds = vec![ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon); n as usize];
    tcx.mk_bound_variable_kinds(&kinds)
}

fn region_from_shape<'tcx>(tcx: TyCtxt<'tcx>, shape: &ArgShape) -> Option<ty::Region<'tcx>> {
    match *shape {
        ArgShape::Lifetime => Some(tcx.lifetimes.re_erased),
        ArgShape::BoundRegion { debruijn, var } => Some(ty::Region::new_bound(
            tcx,
            ty::DebruijnIndex::from_u32(debruijn),
            ty::BoundRegion { var: ty::BoundVar::from_u32(var), kind: ty::BoundRegionKind::Anon },
        )),
        _ => None,
    }
}

fn item_hash(tcx: TyCtxt<'_>, did: DefId) -> HashBytes {
    HashBytes::from(tcx.def_path_hash(did))
}

fn args_to_shapes<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Option<Vec<ArgShape>> {
    args.iter().map(|a| arg_to_shape(tcx, a)).collect()
}

pub fn arg_to_shape<'tcx>(tcx: TyCtxt<'tcx>, arg: GenericArg<'tcx>) -> Option<ArgShape> {
    Some(match arg.kind() {
        GenericArgKind::Lifetime(r) => region_to_shape(r)?,
        GenericArgKind::Type(ty) => ArgShape::Type(ty_to_shape(tcx, ty)?),
        GenericArgKind::Const(ct) => {
            let (ty, bits) = const_scalar(ct)?;
            ArgShape::Const { ty: ty_to_shape(tcx, ty)?, bits: bits.to_string() }
        }
    })
}

fn prim_from_tag<'tcx>(tcx: TyCtxt<'tcx>, tag: &str) -> Option<Ty<'tcx>> {
    let t = &tcx.types;
    Some(match tag {
        "prim:bool" => t.bool,
        "prim:char" => t.char,
        "prim:str" => t.str_,
        "prim:never" => t.never,
        "prim:isize" => t.isize,
        "prim:i8" => t.i8,
        "prim:i16" => t.i16,
        "prim:i32" => t.i32,
        "prim:i64" => t.i64,
        "prim:i128" => t.i128,
        "prim:usize" => t.usize,
        "prim:u8" => t.u8,
        "prim:u16" => t.u16,
        "prim:u32" => t.u32,
        "prim:u64" => t.u64,
        "prim:u128" => t.u128,
        "prim:f16" => t.f16,
        "prim:f32" => t.f32,
        "prim:f64" => t.f64,
        "prim:f128" => t.f128,
        _ => return None,
    })
}

/// Resolves a real `DefPathHash` to a `DefId` in this session, without
/// panicking on hashes from unknown crates or on sentinels.
pub fn def_id_from_hash(tcx: TyCtxt<'_>, hash: DefPathHash) -> Option<DefId> {
    if !tcx.untracked().stable_crate_ids.read().contains_key(&hash.stable_crate_id()) {
        return None;
    }
    tcx.def_path_hash_to_def_id(hash)
}

/// Rebuilds a type from its shape, within `tcx`.
pub fn ty_from_shape<'tcx>(tcx: TyCtxt<'tcx>, shape: &TyShape) -> Option<Ty<'tcx>> {
    Some(match shape {
        TyShape::Primitive(tag) => prim_from_tag(tcx, tag)?,
        TyShape::Adt(hash, arg_shapes) => {
            let did = def_id_from_hash(tcx, DefPathHash::from(*hash))?;
            if !matches!(tcx.def_kind(did), DefKind::Struct | DefKind::Enum | DefKind::Union) {
                return None;
            }
            let args: Vec<GenericArg<'tcx>> =
                arg_shapes.iter().map(|s| arg_from_shape(tcx, s)).collect::<Option<_>>()?;
            if args.len() != tcx.generics_of(did).count() {
                return None;
            }
            Ty::new_adt(tcx, tcx.adt_def(did), tcx.mk_args(&args))
        }
        TyShape::Tuple(elems) => {
            let tys: Vec<Ty<'tcx>> =
                elems.iter().map(|e| ty_from_shape(tcx, e)).collect::<Option<_>>()?;
            Ty::new_tup(tcx, &tys)
        }
        TyShape::Ref(mutable, inner, region) => {
            let mutability = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ref(tcx, region_from_shape(tcx, region)?, ty_from_shape(tcx, inner)?, mutability)
        }
        TyShape::RawPtr(mutable, inner) => {
            let mutability = if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not };
            Ty::new_ptr(tcx, ty_from_shape(tcx, inner)?, mutability)
        }
        TyShape::Slice(inner) => Ty::new_slice(tcx, ty_from_shape(tcx, inner)?),
        TyShape::Array(elem, len) => Ty::new_array(tcx, ty_from_shape(tcx, elem)?, *len),
        TyShape::FnPtr { inputs_and_output, abi, safe, c_variadic, bound_regions } => {
            let tys: Vec<Ty<'tcx>> =
                inputs_and_output.iter().map(|e| ty_from_shape(tcx, e)).collect::<Option<_>>()?;
            let sig = ty::FnSig {
                inputs_and_output: tcx.mk_type_list(&tys),
                c_variadic: *c_variadic,
                safety: if *safe { rustc_hir::Safety::Safe } else { rustc_hir::Safety::Unsafe },
                abi: abi.parse::<rustc_abi::ExternAbi>().ok()?,
            };
            Ty::new_fn_ptr(tcx, ty::Binder::bind_with_vars(sig, anon_region_vars(tcx, *bound_regions)))
        }
        TyShape::Dyn(pred_shapes, region) => {
            let mut preds = Vec::with_capacity(pred_shapes.len());
            for (bound_regions, pred) in pred_shapes {
                let p = match pred {
                    PredShape::Trait(hash, arg_shapes) => {
                        let did = def_id_from_hash(tcx, DefPathHash::from(*hash))?;
                        ty::ExistentialPredicate::Trait(ty::ExistentialTraitRef::new(
                            tcx,
                            did,
                            shapes_to_args(tcx, arg_shapes)?,
                        ))
                    }
                    PredShape::Projection(hash, arg_shapes, term) => {
                        let did = def_id_from_hash(tcx, DefPathHash::from(*hash))?;
                        let term: ty::Term<'tcx> = match arg_from_shape(tcx, term)?.kind() {
                            GenericArgKind::Type(t) => t.into(),
                            GenericArgKind::Const(c) => c.into(),
                            GenericArgKind::Lifetime(_) => return None,
                        };
                        ty::ExistentialPredicate::Projection(ty::ExistentialProjection::new(
                            tcx,
                            did,
                            shapes_to_args(tcx, arg_shapes)?,
                            term,
                        ))
                    }
                    PredShape::AutoTrait(hash) => ty::ExistentialPredicate::AutoTrait(
                        def_id_from_hash(tcx, DefPathHash::from(*hash))?,
                    ),
                };
                preds.push(ty::Binder::bind_with_vars(p, anon_region_vars(tcx, *bound_regions)));
            }
            // Recorded in rustc's canonical order, so interning them back in
            // the same order reproduces the same list.
            let predicates = tcx.mk_poly_existential_predicates(&preds);
            Ty::new_dynamic(tcx, predicates, region_from_shape(tcx, region)?)
        }
        TyShape::Closure(hash, arg_shapes) => {
            let (did, args) = item_from_shape(tcx, hash, arg_shapes, &[DefKind::Closure])?;
            if tcx.is_coroutine(did) {
                return None;
            }
            Ty::new_closure(tcx, did, args)
        }
        TyShape::Coroutine(hash, arg_shapes) => {
            let (did, args) = item_from_shape(tcx, hash, arg_shapes, &[DefKind::Closure])?;
            if !tcx.is_coroutine(did) {
                return None;
            }
            Ty::new_coroutine(tcx, did, args)
        }
        TyShape::CoroutineClosure(hash, arg_shapes) => {
            let (did, args) = item_from_shape(tcx, hash, arg_shapes, &[DefKind::Closure])?;
            if tcx.is_coroutine(did) {
                return None;
            }
            Ty::new_coroutine_closure(tcx, did, args)
        }
        TyShape::FnDef(hash, arg_shapes) => {
            let (did, args) = item_from_shape(
                tcx,
                hash,
                arg_shapes,
                &[
                    DefKind::Fn,
                    DefKind::AssocFn,
                    DefKind::Ctor(CtorOf::Struct, CtorKind::Fn),
                    DefKind::Ctor(CtorOf::Variant, CtorKind::Fn),
                ],
            )?;
            Ty::new_fn_def(tcx, did, args)
        }
        TyShape::Foreign(hash) => {
            let did = def_id_from_hash(tcx, DefPathHash::from(*hash))?;
            if tcx.def_kind(did) != DefKind::ForeignTy {
                return None;
            }
            Ty::new_foreign(tcx, did)
        }
    })
}

fn shapes_to_args<'tcx>(tcx: TyCtxt<'tcx>, shapes: &[ArgShape]) -> Option<Vec<GenericArg<'tcx>>> {
    shapes.iter().map(|s| arg_from_shape(tcx, s)).collect()
}

/// Resolves an item's DefPathHash and rebuilds its args, checking the def
/// kind and arity so a stale or mismatched store can't trip rustc's own
/// (debug-only) argument assertions.
fn item_from_shape<'tcx>(
    tcx: TyCtxt<'tcx>,
    hash: &HashBytes,
    arg_shapes: &[ArgShape],
    kinds: &[DefKind],
) -> Option<(DefId, ty::GenericArgsRef<'tcx>)> {
    let did = def_id_from_hash(tcx, DefPathHash::from(*hash))?;
    if !kinds.contains(&tcx.def_kind(did)) {
        return None;
    }
    let args = shapes_to_args(tcx, arg_shapes)?;
    if args.len() != tcx.generics_of(did).count() {
        return None;
    }
    Some((did, tcx.mk_args(&args)))
}

pub fn arg_from_shape<'tcx>(tcx: TyCtxt<'tcx>, shape: &ArgShape) -> Option<GenericArg<'tcx>> {
    Some(match shape {
        ArgShape::Lifetime | ArgShape::BoundRegion { .. } => region_from_shape(tcx, shape)?.into(),
        ArgShape::Type(t) => ty_from_shape(tcx, t)?.into(),
        ArgShape::Const { ty, bits } => {
            let ty = ty_from_shape(tcx, ty)?;
            // Const::from_bits needs a layout; only scalar types get here
            // via arg_to_shape, but a hand-edited store shouldn't ICE.
            if !(ty.is_integral() || ty.is_bool() || ty.is_char()) {
                return None;
            }
            let bits: u128 = bits.parse().ok()?;
            ty::Const::from_bits(tcx, bits, TypingEnv::fully_monomorphized(), ty).into()
        }
    })
}

/// Hash -> shape table for every sentinel a process has computed or read.
/// Each side keeps its own instance (a `static`), seeded on the reading
/// side from the store.
pub struct ShapeRegistry(OnceLock<Mutex<FxHashMap<DefPathHash, ArgShape>>>);

impl ShapeRegistry {
    pub const fn new() -> Self {
        ShapeRegistry(OnceLock::new())
    }

    fn map(&self) -> MutexGuard<'_, FxHashMap<DefPathHash, ArgShape>> {
        self.0.get_or_init(|| Mutex::new(FxHashMap::default())).lock().unwrap()
    }

    pub fn record(&self, hash: DefPathHash, shape: ArgShape) {
        self.map().insert(hash, shape);
    }

    pub fn get(&self, hash: &DefPathHash) -> Option<ArgShape> {
        self.map().get(hash).cloned()
    }

    pub fn snapshot(&self) -> FxHashMap<DefPathHash, ArgShape> {
        self.map().clone()
    }

    /// Adds every entry of `shapes` not already present.
    // Order-independent: each entry is inserted independently.
    #[allow(rustc::potential_query_instability)]
    pub fn seed(&self, shapes: &FxHashMap<DefPathHash, ArgShape>) {
        let mut map = self.map();
        for (hash, shape) in shapes {
            map.entry(*hash).or_insert_with(|| shape.clone());
        }
    }
}

/// Rebuilds a generic argument from its hash: the fixed lifetime sentinel,
/// a real DefPathHash of a non-generic ADT, or a sentinel with a recorded
/// shape.
pub fn arg_from_hash<'tcx>(
    tcx: TyCtxt<'tcx>,
    hash: DefPathHash,
    shapes: &ShapeRegistry,
) -> Option<GenericArg<'tcx>> {
    if hash == lifetime_arg_hash() {
        return Some(tcx.lifetimes.re_erased.into());
    }
    if let Some(did) = def_id_from_hash(tcx, hash) {
        return Some(tcx.type_of(did).instantiate_identity().into());
    }
    arg_from_shape(tcx, &shapes.get(&hash)?)
}
