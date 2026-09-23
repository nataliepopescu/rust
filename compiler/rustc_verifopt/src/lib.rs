//! The type-hashing scheme and store format shared by verifopt's two
//! halves: the analysis (a rustc driver plugin that sees types through
//! rustc_public) and the rewrite (`rustc_codegen_ssa::mir::verifopt_rewrite`,
//! which sees rustc_middle types directly).
//!
//! Both halves must compute byte-identical hashes for the same type, since
//! the analysis writes store entries keyed by those hashes and the rewrite
//! looks them up by recomputing them. Previously each side carried its own
//! copy of this code; keeping it here means there is only one definition
//! to get right. Everything operates on rustc_middle types - the plugin
//! converts from rustc_public with `rustc_internal::internal` first.
//!
//! The crate also owns the JSON encoding of the store (see [`Store`]). The
//! plugin and the compiler link *different* copies of `serde` (crates.io
//! vs the compiler's own), so serde-derived types can't cross between them;
//! both sides go through [`Store::to_json`]/[`Store::from_json`] instead.

mod hash;
mod shape;
mod store;

pub use hash::{hash_arg, hash_args, hash_ty, lifetime_arg_hash};
pub use shape::{
    ArgShape, HashBytes, ShapeRegistry, TyShape, arg_from_hash, arg_from_shape, arg_to_shape,
    def_id_from_hash, ty_from_shape, ty_to_shape,
};
pub use store::{SiteKey, Store, TagSite, Target};
