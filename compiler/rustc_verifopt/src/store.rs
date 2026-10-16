//! The analysis -> rewrite store, and its on-disk JSON encoding.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_span::def_id::DefPathHash;
use serde::{Deserialize, Serialize};

use crate::shape::{ArgShape, HashBytes};

/// A dispatch site: (caller fn's DefPathHash, bb, hashes of the caller
/// instance's *resolved* generic args - i.e. `Instance::args`, which is what
/// codegen sees).
pub type SiteKey = (DefPathHash, usize, Vec<DefPathHash>);

/// A target: (impl fn's DefPathHash, hashes of its generic args, when
/// resolvable).
pub type Target = (DefPathHash, Option<Vec<DefPathHash>>);

/// A tagged site: (bb, stmt, tag, impl fn, concrete generic args).
pub type TagSite = (usize, usize, u64, DefPathHash, Option<Vec<DefPathHash>>);

#[derive(Default)]
pub struct Store {
    pub targets: FxHashMap<SiteKey, Vec<Target>>,
    pub tags: FxHashMap<SiteKey, Vec<TagSite>>,
    /// Every sentinel hash referenced above, with the shape it came from.
    pub shapes: FxHashMap<DefPathHash, ArgShape>,
    /// Name -> stable crate id of every crate containing a stored site, as
    /// the analysis saw it. Every DefPathHash in the keys starts with its
    /// crate's stable crate id, which cargo derives (via `-C metadata`) from
    /// the package *and the build profile, features, ...*. So if a crate of
    /// this name is compiled with a different id, the store came from a
    /// differently configured build and none of its keys can match - which
    /// otherwise fails silently. See `crate_id_mismatch`.
    pub crates: FxHashMap<String, u64>,
    /// Sites whose single target is an *exact instance*: its argument hashes
    /// are that function's own generic args (from the instance manifests),
    /// not - as for every other target - the Self ADT's args. The analysis
    /// records these where CHAmax shows exactly one instance in the whole
    /// program can be reached (a provably single target, even where FSA fell
    /// back to CHA), and the rewrite builds that instance as is.
    pub exact: FxHashSet<SiteKey>,
}

/// Where the analysis writes the store and the rewrite reads it:
/// `$VERIFOPT_STORE_DIR/verifopt_store.json`, else
/// `verifopt_results/verifopt_store.json` (cargo-verifopt always sets the
/// variable for the rustc processes it starts).
pub fn store_path() -> std::path::PathBuf {
    results_dir().join("verifopt_store.json")
}

/// The run's results directory: `$VERIFOPT_STORE_DIR` (cargo-verifopt always
/// sets it for the rustc processes it starts), else `verifopt_results`.
pub fn results_dir() -> std::path::PathBuf {
    match std::env::var_os("VERIFOPT_STORE_DIR") {
        Some(dir) => std::path::PathBuf::from(dir),
        None => std::path::PathBuf::from("verifopt_results"),
    }
}

/// Reads and parses the store at `store_path()`.
pub fn load_store() -> Result<Store, String> {
    let path = store_path();
    let contents = std::fs::read_to_string(&path)
        .map_err(|e| format!("could not read {}: {e}", path.display()))?;
    Store::from_json(&contents).map_err(|e| format!("could not parse {}: {e}", path.display()))
}

impl Store {
    /// If the store has sites in a crate named `crate_name` but recorded it
    /// with a different stable crate id than `crate_id` (this compilation's),
    /// returns the recorded id: the store doesn't describe this build.
    pub fn crate_id_mismatch(&self, crate_name: &str, crate_id: u64) -> Option<u64> {
        self.crates.get(crate_name).copied().filter(|recorded| *recorded != crate_id)
    }
}

type SerKey = (HashBytes, usize, Vec<HashBytes>);

#[derive(Serialize, Deserialize, Default)]
struct SerStore {
    targets: Vec<(SerKey, Vec<(HashBytes, Option<Vec<HashBytes>>)>)>,
    tags: Vec<(SerKey, Vec<(usize, usize, u64, HashBytes, Option<Vec<HashBytes>>)>)>,
    #[serde(default)]
    shapes: Vec<(HashBytes, ArgShape)>,
    #[serde(default)]
    crates: Vec<(String, u64)>,
    #[serde(default)]
    exact: Vec<SerKey>,
}

fn ser_vec(v: &[DefPathHash]) -> Vec<HashBytes> {
    v.iter().map(|h| HashBytes::from(*h)).collect()
}

fn de_vec(v: Vec<HashBytes>) -> Vec<DefPathHash> {
    v.into_iter().map(DefPathHash::from).collect()
}

fn ser_key((h, bb, args): &SiteKey) -> SerKey {
    (HashBytes::from(*h), *bb, ser_vec(args))
}

fn de_key((h, bb, args): SerKey) -> SiteKey {
    (DefPathHash::from(h), bb, de_vec(args))
}

impl Store {
    // Entry order in the output is arbitrary but never read back as
    // meaningful: every entry is re-inserted into a map by from_json.
    #[allow(rustc::potential_query_instability)]
    pub fn to_json(&self) -> Result<String, String> {
        let ser = SerStore {
            targets: self
                .targets
                .iter()
                .map(|(k, v)| {
                    let v = v
                        .iter()
                        .map(|(h, args)| (HashBytes::from(*h), args.as_deref().map(ser_vec)))
                        .collect();
                    (ser_key(k), v)
                })
                .collect(),
            tags: self
                .tags
                .iter()
                .map(|(k, v)| {
                    let v = v
                        .iter()
                        .map(|(bb, stmt, tag, h, args)| {
                            (*bb, *stmt, *tag, HashBytes::from(*h), args.as_deref().map(ser_vec))
                        })
                        .collect();
                    (ser_key(k), v)
                })
                .collect(),
            shapes: self.shapes.iter().map(|(h, s)| (HashBytes::from(*h), s.clone())).collect(),
            crates: self.crates.iter().map(|(n, id)| (n.clone(), *id)).collect(),
            exact: self.exact.iter().map(ser_key).collect(),
        };
        serde_json::to_string(&ser).map_err(|e| e.to_string())
    }

    pub fn from_json(json: &str) -> Result<Store, String> {
        let ser: SerStore = serde_json::from_str(json).map_err(|e| e.to_string())?;
        Ok(Store {
            targets: ser
                .targets
                .into_iter()
                .map(|(k, v)| {
                    let v = v
                        .into_iter()
                        .map(|(h, args)| (DefPathHash::from(h), args.map(de_vec)))
                        .collect();
                    (de_key(k), v)
                })
                .collect(),
            tags: ser
                .tags
                .into_iter()
                .map(|(k, v)| {
                    let v = v
                        .into_iter()
                        .map(|(bb, stmt, tag, h, args)| {
                            (bb, stmt, tag, DefPathHash::from(h), args.map(de_vec))
                        })
                        .collect();
                    (de_key(k), v)
                })
                .collect(),
            shapes: ser.shapes.into_iter().map(|(h, s)| (DefPathHash::from(h), s)).collect(),
            crates: ser.crates.into_iter().collect(),
            exact: ser.exact.into_iter().map(de_key).collect(),
        })
    }
}
