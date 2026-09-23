//! The analysis -> rewrite store, and its on-disk JSON encoding.

use rustc_data_structures::fx::FxHashMap;
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
}

type SerKey = (HashBytes, usize, Vec<HashBytes>);

#[derive(Serialize, Deserialize, Default)]
struct SerStore {
    targets: Vec<(SerKey, Vec<(HashBytes, Option<Vec<HashBytes>>)>)>,
    tags: Vec<(SerKey, Vec<(usize, usize, u64, HashBytes, Option<Vec<HashBytes>>)>)>,
    #[serde(default)]
    shapes: Vec<(HashBytes, ArgShape)>,
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
        })
    }
}
