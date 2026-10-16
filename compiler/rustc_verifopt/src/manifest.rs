//! Per-crate instance manifests, for verifopt's "CHAmax".
//!
//! CHA lists which trait impls (methods) could implement a dispatched trait
//! method. That's a sound maximum at the level of *impls* - but a generic impl
//! (e.g. `impl<C, D> Process for ProcessStandard<'_, C, D>`) stands for many
//! functions, one per instantiation, and which instantiations exist is only
//! known per crate, after monomorphization. So every crate compiled under
//! cargo-verifopt records the instances it compiles of trait methods
//! (implementations and default bodies) and closures, and the analysis unions
//! them over the whole program: CHAmax = every compiled instance of a site's
//! CHA candidates. Written by rustc_monomorphize's partitioning, read by the
//! analysis plugin.

use rustc_data_structures::fx::FxHashMap;
use rustc_span::def_id::DefPathHash;
use serde::{Deserialize, Serialize};

use crate::shape::{ArgShape, HashBytes};

/// The instances one crate compiles, as (DefPathHash of the function, hashes
/// of its generic args - `None` if they couldn't be hashed).
pub struct InstanceManifest {
    pub crate_name: String,
    pub crate_id: u64,
    pub instances: Vec<(DefPathHash, Option<Vec<DefPathHash>>)>,
    /// The shapes of the sentinel hashes in `instances` - needed to turn a
    /// generic argument like `ProcessStandard<'_, Sam4l, ..>` back into a type
    /// (rustc_verifopt::arg_from_hash), e.g. when the analysis records one of
    /// these instances as an exact target (Store::exact).
    pub shapes: FxHashMap<DefPathHash, ArgShape>,
}

#[derive(Serialize, Deserialize)]
struct SerManifest {
    crate_name: String,
    crate_id: u64,
    instances: Vec<(HashBytes, Option<Vec<HashBytes>>)>,
    #[serde(default)]
    shapes: Vec<(HashBytes, ArgShape)>,
}

impl InstanceManifest {
    pub fn to_json(&self) -> Result<String, String> {
        let ser = SerManifest {
            crate_name: self.crate_name.clone(),
            crate_id: self.crate_id,
            instances: self
                .instances
                .iter()
                .map(|(h, args)| {
                    (HashBytes::from(*h), args.as_ref().map(|a| a.iter().map(|x| HashBytes::from(*x)).collect()))
                })
                .collect(),
            shapes: shapes_sorted(&self.shapes),
        };
        serde_json::to_string(&ser).map_err(|e| e.to_string())
    }

    pub fn from_json(json: &str) -> Result<InstanceManifest, String> {
        let ser: SerManifest = serde_json::from_str(json).map_err(|e| e.to_string())?;
        Ok(InstanceManifest {
            crate_name: ser.crate_name,
            crate_id: ser.crate_id,
            instances: ser
                .instances
                .into_iter()
                .map(|(h, args)| {
                    (DefPathHash::from(h), args.map(|a| a.into_iter().map(DefPathHash::from).collect()))
                })
                .collect(),
            shapes: ser.shapes.into_iter().map(|(h, s)| (DefPathHash::from(h), s)).collect(),
        })
    }
}

// Sorted, so a manifest's bytes don't depend on hash-map order.
#[allow(rustc::potential_query_instability)]
fn shapes_sorted(shapes: &FxHashMap<DefPathHash, ArgShape>) -> Vec<(HashBytes, ArgShape)> {
    let mut v: Vec<(DefPathHash, ArgShape)> = shapes.iter().map(|(h, s)| (*h, s.clone())).collect();
    v.sort_by_key(|(h, _)| *h);
    v.into_iter().map(|(h, s)| (HashBytes::from(h), s)).collect()
}

/// `<results dir>/instance_manifests`, one `<crate>-<stable crate id>.json`
/// per compiled crate.
pub fn manifest_dir() -> std::path::PathBuf {
    crate::store::results_dir().join("instance_manifests")
}
