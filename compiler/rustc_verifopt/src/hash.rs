//! Stable, cross-process type hashes.
//!
//! A hash is a `DefPathHash`. Nominal types without generic args use their
//! real `DefPathHash` (so the reading side can resolve them back to a
//! `DefId` directly). Everything else - primitives, compound types, generic
//! ADTs, lifetimes, consts - uses a *sentinel*: an FNV-1a hash of a
//! structural tag. Sentinels are one-way, so each one is paired with an
//! [`crate::ArgShape`] (recorded via [`hash_args`]) that the reading side
//! uses to rebuild the type.

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_middle::ty::{self, GenericArg, GenericArgKind, GenericArgsRef, Ty, TyCtxt};
use rustc_span::def_id::DefPathHash;

use crate::shape::{ShapeRegistry, arg_to_shape};

/// FNV-1a over `tag`, split into two differently-salted 64-bit halves.
/// Deliberately simple and self-contained: this value is written to disk by
/// one process and recomputed by another.
pub(crate) fn sentinel(tag: &str) -> DefPathHash {
    fn fnv1a_64(bytes: &[u8]) -> u64 {
        let mut hash: u64 = 0xcbf29ce484222325;
        for &b in bytes {
            hash ^= b as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }
    let h1 = fnv1a_64(tag.as_bytes());
    let h2 = fnv1a_64(format!("{tag}#verifopt-sentinel").as_bytes());
    DefPathHash(Fingerprint::new(h1, h2))
}

/// Combines a tag with an ordered list of nested hashes into one sentinel.
pub(crate) fn combine(tag: &str, hashes: &[DefPathHash]) -> DefPathHash {
    let joined = hashes.iter().map(|h| format!("{h:?}")).collect::<Vec<_>>().join(",");
    sentinel(&format!("{tag}:[{joined}]"))
}

/// The single hash every lifetime argument maps to. Regions are erased
/// throughout the pipeline, so all lifetimes are equivalent; they still get
/// a slot of their own so that a hashed arg list keeps the same length (and
/// positions) as the `GenericArgs` it came from.
pub fn lifetime_arg_hash() -> DefPathHash {
    sentinel("arg:lifetime")
}

/// Tag for a primitive (leaf) type, shared with shape reconstruction.
pub(crate) fn prim_tag(ty: Ty<'_>) -> Option<&'static str> {
    Some(match ty.kind() {
        ty::Bool => "prim:bool",
        ty::Char => "prim:char",
        ty::Str => "prim:str",
        ty::Never => "prim:never",
        ty::Int(int_ty) => match int_ty {
            ty::IntTy::Isize => "prim:isize",
            ty::IntTy::I8 => "prim:i8",
            ty::IntTy::I16 => "prim:i16",
            ty::IntTy::I32 => "prim:i32",
            ty::IntTy::I64 => "prim:i64",
            ty::IntTy::I128 => "prim:i128",
        },
        ty::Uint(uint_ty) => match uint_ty {
            ty::UintTy::Usize => "prim:usize",
            ty::UintTy::U8 => "prim:u8",
            ty::UintTy::U16 => "prim:u16",
            ty::UintTy::U32 => "prim:u32",
            ty::UintTy::U64 => "prim:u64",
            ty::UintTy::U128 => "prim:u128",
        },
        ty::Float(float_ty) => match float_ty {
            ty::FloatTy::F16 => "prim:f16",
            ty::FloatTy::F32 => "prim:f32",
            ty::FloatTy::F64 => "prim:f64",
            ty::FloatTy::F128 => "prim:f128",
        },
        _ => return None,
    })
}

/// The scalar value of a fully-evaluated const, as (type, raw bits).
pub(crate) fn const_scalar<'tcx>(ct: ty::Const<'tcx>) -> Option<(Ty<'tcx>, u128)> {
    let value = ct.try_to_value()?;
    let leaf = value.try_to_leaf()?;
    Some((value.ty, leaf.to_bits(leaf.size())))
}

/// Hashes one type, or returns `None` if its shape isn't supported (e.g. a
/// closure, a still-generic param, or a multi-predicate `dyn`).
pub fn hash_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefPathHash> {
    if let Some(tag) = prim_tag(ty) {
        return Some(sentinel(tag));
    }
    Some(match ty.kind() {
        ty::Adt(adt_def, args) => {
            let def_hash = tcx.def_path_hash(adt_def.did());
            if args.is_empty() {
                // Unchanged from the original scheme: a plain nominal type
                // is its own DefPathHash, resolvable back to a DefId.
                def_hash
            } else {
                let mut hashes = vec![def_hash];
                for arg in args.iter() {
                    hashes.push(hash_arg(tcx, arg)?);
                }
                combine("adt", &hashes)
            }
        }
        ty::Tuple(elems) => {
            let hashes: Vec<DefPathHash> =
                elems.iter().map(|t| hash_ty(tcx, t)).collect::<Option<_>>()?;
            combine("prim:tuple", &hashes)
        }
        ty::Ref(_region, inner, mutability) => {
            let tag = if mutability.is_mut() { "prim:ref:mut" } else { "prim:ref:not" };
            combine(tag, &[hash_ty(tcx, *inner)?])
        }
        ty::RawPtr(inner, mutability) => {
            let tag = if mutability.is_mut() { "prim:rawptr:mut" } else { "prim:rawptr:not" };
            combine(tag, &[hash_ty(tcx, *inner)?])
        }
        ty::Slice(inner) => combine("prim:slice", &[hash_ty(tcx, *inner)?]),
        ty::Array(elem, len) => {
            let len = len.try_to_target_usize(tcx)?;
            combine("prim:array", &[hash_ty(tcx, *elem)?, sentinel(&format!("len:{len}"))])
        }
        ty::FnPtr(sig_tys, fn_header) => {
            let mut hashes: Vec<DefPathHash> = sig_tys
                .skip_binder()
                .inputs_and_output
                .iter()
                .map(|t| hash_ty(tcx, t))
                .collect::<Option<_>>()?;
            hashes.push(sentinel(&format!(
                "prim:fnptr:header:{}:{}:{}",
                fn_header.abi.name(),
                fn_header.safety.is_safe(),
                fn_header.c_variadic,
            )));
            combine("prim:fnptr", &hashes)
        }
        // Only a single plain trait predicate is handled (no auto traits,
        // no associated-type bindings).
        ty::Dynamic(predicates, _region) => {
            let [binder] = predicates.as_slice() else {
                return None;
            };
            let ty::ExistentialPredicate::Trait(trait_ref) = binder.skip_binder() else {
                return None;
            };
            let mut hashes = vec![tcx.def_path_hash(trait_ref.def_id)];
            for arg in trait_ref.args.iter() {
                hashes.push(hash_arg(tcx, arg)?);
            }
            combine("prim:dyn", &hashes)
        }
        _ => return None,
    })
}

/// Hashes one generic argument. Lifetimes all map to
/// [`lifetime_arg_hash`]; consts are supported when they evaluate to a
/// scalar.
pub fn hash_arg<'tcx>(tcx: TyCtxt<'tcx>, arg: GenericArg<'tcx>) -> Option<DefPathHash> {
    match arg.kind() {
        GenericArgKind::Lifetime(_) => Some(lifetime_arg_hash()),
        GenericArgKind::Type(ty) => hash_ty(tcx, ty),
        GenericArgKind::Const(ct) => {
            let (ty, bits) = const_scalar(ct)?;
            Some(combine("arg:const", &[hash_ty(tcx, ty)?, sentinel(&format!("bits:{bits}"))]))
        }
    }
}

/// Hashes a whole argument list, position by position, recording each
/// argument's shape in `shapes` so the reading side can rebuild it.
/// Returns `None` if any argument can't be hashed; callers must then treat
/// the thing being keyed as unrewritable rather than fall back to a
/// coarser key.
pub fn hash_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: GenericArgsRef<'tcx>,
    shapes: &ShapeRegistry,
) -> Option<Vec<DefPathHash>> {
    let mut hashes = Vec::with_capacity(args.len());
    for arg in args.iter() {
        let hash = hash_arg(tcx, arg)?;
        if let Some(shape) = arg_to_shape(tcx, arg) {
            shapes.record(hash, shape);
        }
        hashes.push(hash);
    }
    Some(hashes)
}
