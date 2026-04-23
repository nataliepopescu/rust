use std::fmt;

use rustc_ast::Mutability;
use rustc_macros::HashStable;
use rustc_type_ir::elaborate;

use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;

use tracing::debug;

use crate::mir::interpret::{
    AllocId, AllocInit, Allocation, Scalar, alloc_range,
};
use crate::ty::{self, DefId, Instance, TraitRef, Ty, TyCtxt, TyKind};

#[derive(Clone, Copy, PartialEq, HashStable)]
pub enum VtblEntry<'tcx> {
    /// destructor of this type (used in vtable header)
    MetadataDropInPlace,
    /// layout size of this type (used in vtable header)
    MetadataSize,
    /// layout align of this type (used in vtable header)
    MetadataAlign,
    /// non-dispatchable associated function that is excluded from trait object
    Vacant,
    /// dispatchable associated function
    Method(Instance<'tcx>),
    /// pointer to a separate supertrait vtable, can be used by trait upcasting coercion
    TraitVPtr(TraitRef<'tcx>),
}

impl<'tcx> fmt::Debug for VtblEntry<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We want to call `Display` on `Instance` and `PolyTraitRef`,
        // so we implement this manually.
        match self {
            VtblEntry::MetadataDropInPlace => write!(f, "MetadataDropInPlace"),
            VtblEntry::MetadataSize => write!(f, "MetadataSize"),
            VtblEntry::MetadataAlign => write!(f, "MetadataAlign"),
            VtblEntry::Vacant => write!(f, "Vacant"),
            VtblEntry::Method(instance) => write!(f, "Method({instance})"),
            VtblEntry::TraitVPtr(trait_ref) => write!(f, "TraitVPtr({trait_ref})"),
        }
    }
}

// Needs to be associated with the `'tcx` lifetime
impl<'tcx> TyCtxt<'tcx> {
    pub const COMMON_VTABLE_ENTRIES: &'tcx [VtblEntry<'tcx>] =
        &[VtblEntry::MetadataDropInPlace, VtblEntry::MetadataSize, VtblEntry::MetadataAlign];
}

pub const COMMON_VTABLE_ENTRIES_DROPINPLACE: usize = 0;
pub const COMMON_VTABLE_ENTRIES_SIZE: usize = 1;
pub const COMMON_VTABLE_ENTRIES_ALIGN: usize = 2;

// Note that we don't have access to a self type here, this has to be purely based on the trait (and
// supertrait) definitions. That means we can't call into the same vtable_entries code since that
// returns a specific instantiation (e.g., with Vacant slots when bounds aren't satisfied). The goal
// here is to do a best-effort approximation without duplicating a lot of code.
//
// This function is used in layout computation for e.g. &dyn Trait, so it's critical that this
// function is an accurate approximation. We verify this when actually computing the vtable below.
pub(crate) fn vtable_min_entries<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: Option<ty::ExistentialTraitRef<'tcx>>,
) -> usize {
    let mut count = TyCtxt::COMMON_VTABLE_ENTRIES.len();
    let Some(trait_ref) = trait_ref else {
        return count;
    };

    // This includes self in supertraits.
    for def_id in elaborate::supertrait_def_ids(tcx, trait_ref.def_id) {
        count += tcx.own_existential_vtable_entries(def_id).len();
    }

    count
}

fn get_ty_id<'tcx>(_tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> u128 {
    let file = File::open("/home/np/hack/verifopt/analysis/defids").unwrap();
    let reader = BufReader::new(file);

    debug!("IN GET_TY_ID");
    debug!("ty: {:?}", ty);
    debug!("ty.kind: {:?}", ty.kind());

    match ty.kind() {
        TyKind::Adt(ty_def, _) => {
            let ty_defid = ty_def.did();
            debug!("---ADT: {:?}", ty_defid);
            for line in reader.lines() {
                let line = line.unwrap();
                let v: Vec<&str> = line.split('-').collect();
                let struct_defid_path = v.get(0).unwrap();
                let id = v.get(1).unwrap();
                debug!("id: {:?}", id);
                debug!("struct defid path: {:?}", struct_defid_path);

                let v2: Vec<&str> = struct_defid_path.split("~").collect();
                let defid_prefix = v2.get(0).unwrap();
                debug!("defid_prefix: {:?}", defid_prefix);

                let v3: Vec<&str> = defid_prefix.split("(").collect();
                let defid_nums = v3.get(1).unwrap();
                debug!("defid_nums: {:?}", defid_nums);

                let v4: Vec<&str> = defid_nums.trim().split(":").collect();
                let crate_num: usize = v4.get(0).unwrap().parse().unwrap();
                let def_index: usize = v4.get(1).unwrap().parse().unwrap();
                debug!("crate_num: {:?}", crate_num);
                debug!("def_index: {:?}", def_index);

                let struct_defid = DefId { index: def_index.into(), krate: crate_num.into() };

                if ty_defid == struct_defid {
                    debug!("EQ!!!");
                    return id.parse().unwrap();
                }
            }
            3001
        }
        TyKind::Closure(defid, _) => {
            debug!("---CLOSURE: {:?}", defid);
            3002
        }
        _ => {
            debug!("---OTHER");
            3000
        }
    }
}

/// Retrieves an allocation that represents the contents of a vtable.
/// Since this is a query, allocations are cached and not duplicated.
///
/// This is an "internal" `AllocId` that should never be used as a value in the interpreted program.
/// The interpreter should use `AllocId` that refer to a `GlobalAlloc::VTable` instead.
/// (This is similar to statics, which also have a similar "internal" `AllocId` storing their
/// initial contents.)
pub(super) fn vtable_allocation_provider<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: (Ty<'tcx>, Option<ty::ExistentialTraitRef<'tcx>>),
) -> AllocId {
    let (ty, _poly_trait_ref) = key;

    //let vtable_entries = if let Some(poly_trait_ref) = poly_trait_ref {
    //    let trait_ref = poly_trait_ref.with_self_ty(tcx, ty);
    //    let trait_ref = tcx.erase_and_anonymize_regions(trait_ref);

    //    tcx.vtable_entries(trait_ref)
    //} else {
    //    TyCtxt::COMMON_VTABLE_ENTRIES
    //};

    // This confirms that the layout computation for &dyn Trait has an accurate sizing.
    //assert!(vtable_entries.len() >= vtable_min_entries(tcx, poly_trait_ref));

    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        .expect("failed to build vtable representation");
    assert!(layout.is_sized(), "can't create a vtable for an unsized type");
    //let size = layout.size.bytes();
    //let align = layout.align.bytes();

    let ptr_size = tcx.data_layout.pointer_size();
    let ptr_align = tcx.data_layout.pointer_align().abi;

    //let vtable_size = ptr_size; // * u64::try_from(vtable_entries.len()).unwrap();

    // Empty (zero-sized) allocation
    let mut vtable = Allocation::new(ptr_size, ptr_align, AllocInit::Uninit, ());

    // No need to do any alignment checks on the memory accesses below, because we know the
    // allocation is correctly aligned as we created it above. Also we're only offsetting by
    // multiples of `ptr_align`, which means that it will stay aligned to `ptr_align`.

    /*
    for (idx, entry) in vtable_entries.iter().enumerate() {
        let idx: u64 = u64::try_from(idx).unwrap();
        let scalar = match *entry {
            VtblEntry::MetadataDropInPlace => {
                if ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
                    let instance = ty::Instance::resolve_drop_in_place(tcx, ty);
                    let fn_alloc_id = tcx.reserve_and_set_fn_alloc(instance, CTFE_ALLOC_SALT);
                    let fn_ptr = Pointer::from(fn_alloc_id);
                    Scalar::from_pointer(fn_ptr, &tcx)
                } else {
                    Scalar::from_maybe_pointer(Pointer::null(), &tcx)
                }
            }
            VtblEntry::MetadataSize => Scalar::from_uint(size, ptr_size),
            VtblEntry::MetadataAlign => Scalar::from_uint(align, ptr_size),
            VtblEntry::Vacant => continue,
            VtblEntry::Method(instance) => {
                // Prepare the fn ptr we write into the vtable.
                let fn_alloc_id = tcx.reserve_and_set_fn_alloc(instance, CTFE_ALLOC_SALT);
                let fn_ptr = Pointer::from(fn_alloc_id);
                Scalar::from_pointer(fn_ptr, &tcx)
            }
            VtblEntry::TraitVPtr(trait_ref) => {
                let super_trait_ref = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);
                let supertrait_alloc_id = tcx.vtable_allocation((ty, Some(super_trait_ref)));
                let vptr = Pointer::from(supertrait_alloc_id);
                Scalar::from_pointer(vptr, &tcx)
            }
        };
        vtable
            .write_scalar(&tcx, alloc_range(ptr_size * idx, ptr_size), scalar)
            .expect("failed to build vtable representation");
    }
    */

    let val = get_ty_id(tcx, ty);
    let scalar = Scalar::from_uint(val, ptr_size);
    vtable.write_scalar(&tcx, alloc_range(ptr_size * 0, ptr_size), scalar)
        .expect("failed to build vtable representation");

    vtable.mutability = Mutability::Not;
    tcx.reserve_and_set_memory_alloc(tcx.mk_const_alloc(vtable))
}
