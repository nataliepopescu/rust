use rustc_middle::ty::{Ty, TyCtxt};
//use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
//use rustc_data_structures::fingerprint::Fingerprint;

use tracing::info;

pub(super) fn ty_tag_provider<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>
) -> usize {
    //3000
    //let mut hcx = tcx._stable_hashing_context();
    //let mut hasher = StableHasher::new();

    // Optional but recommended:
    let ty = tcx.erase_and_anonymize_regions(ty);

    let tag: usize = tcx.type_id_hash(ty).truncate().as_u64().try_into().unwrap();

    //ty.hash_stable(&mut hcx, &mut hasher);

    //let fingerprint: Fingerprint = hasher.finish();

    //let tag: usize = fingerprint.to_smaller_hash().as_u64().try_into().unwrap();
    info!("ty_tag({:?}) = {}", ty, tag);
    tag
}
