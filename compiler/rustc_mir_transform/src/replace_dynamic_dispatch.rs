//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent
//! statically dispatched function calls.

#![allow(dead_code)]
//#![allow(unused_variables)]

//use std::ops::Index;

// FIXME precise imports

use rustc_abi::FieldIdx;
//use rustc_middle::mir::{Statement, Terminator, StatementKind, TerminatorKind, Operand, CastKind, Rvalue, BinOp, PlaceElem, PlaceRef, Place, UnwindAction, CallSource, ConstOperand, ConstValue, Local, ProjectionElem, BasicBlock, BasicBlockData, RawPtrKind, Location, SwitchTargets, SourceInfo, SourceScope, Body, TerminatorEdges};
use rustc_middle::mir::*;
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::*;
use rustc_span::def_id::*;
use rustc_span::source_map::Spanned;
use rustc_span::*;
use tracing::debug;

use crate::patch::MirPatch;

pub(super) struct ReplaceDynamicDispatch;

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        debug!("for func @ {:?}", body.span);
        debug!("LOCALS BEFORE ({:?})", body.local_decls().len());
        for (idx, local_decl) in body.local_decls().iter_enumerated() {
            debug!("-------idx: {:?}", idx);
            debug!("local_decl: {:?}", local_decl);
            debug!("mutability: {:?}", local_decl.mutability);
            debug!("ty: {:?}", local_decl.ty);
            id_ty(local_decl.ty);
        }

        debug!("RUN PASS");
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            debug!("BB: {:?}", bb);
            id_term(tcx, &data.terminator().kind);
            match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    if let Some((defid, rawlist)) = func.const_fn_def() {
                        if tcx.def_path_debug_str(defid).contains("Animal::speak") {
                            let ty = rawlist.type_at(0);
                            id_ty(ty);
                            if ty.is_trait() {
                                debug!("ty: {:?}", ty);
                                let num_bbs = body.basic_blocks.len();
                                replace_dynamic_dispatch(tcx, &mut patch, ty, bb, data, num_bbs);
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        patch.apply(body);
    }

    fn is_required(&self) -> bool {
        true
    }
}

fn get_dids<'tcx>(
    tcx: TyCtxt<'tcx>,
    simplified_ty: &SimplifiedType,
    assoc_items_did: DefId,
) -> (DefId, DefId) {
    let ty_did;
    match simplified_ty {
        SimplifiedType::Adt(inner_did) => ty_did = inner_did,
        _ => panic!("impl is not Adt"),
    }

    // dummy init value b/c the compiler thinks we can
    // proceed with an uninit value despite the `init` flag
    let mut init = false;
    // FIXME
    let mut fn_did = DefId { index: DefIndex::from_u32(0), krate: CrateNum::from_u32(0) };
    for assoc_item in tcx.associated_items(assoc_items_did).in_definition_order() {
        debug!("assoc_item: {:?}", assoc_item);
        debug!("assoc_item.def_id: {:?}", assoc_item.def_id);
        fn_did = assoc_item.def_id;
        init = true;
    }
    if !init {
        panic!("no assoc items!");
    }

    (*ty_did, fn_did)
}

fn replace_dynamic_dispatch<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    ty: Ty<'tcx>,
    bb: BasicBlock,
    data: &BasicBlockData<'tcx>,
    num_bbs: usize,
) {
    debug!("-----REPLACE");

    // TODO make top-level empty_projs + dummy_spans

    let traitobj_did: DefId;
    match ty.kind() {
        Dynamic(rawlist, ..) => {
            if rawlist.len() > 0 {
                let principal_did_opt = (*rawlist).principal_def_id();
                if let Some(did) = principal_did_opt {
                    traitobj_did = did;
                } else {
                    debug!("auto traits only - nothing to replace");
                    return;
                }
            } else {
                return;
            }
        }
        // realistically can just return, but panicking for now to see
        // if this is ever triggered
        _ => panic!("trait is not Dynamic"),
    }

    // get trait impl defids
    // alternatively, replace trait_impls_of() => all_impls()
    let impls = tcx.trait_impls_of(traitobj_did);
    let blanket_impls_dids = impls.blanket_impls();
    let nb_impls_dids = impls.non_blanket_impls();
    let impls_keys: Vec<_> = nb_impls_dids.keys().collect();
    let impls_vals: Vec<_> = nb_impls_dids.values().collect();
    debug!("blanket dids: {:?}", blanket_impls_dids);
    debug!("non-blanket dids: {:?}", nb_impls_dids);
    debug!("impls_keys: {:?}", impls_keys);
    debug!("impls_values: {:?}", impls_vals);

    debug!("CAT DIDS");
    let (cat_did, cat_speak_did) =
        get_dids(tcx, impls_keys.get(0).unwrap(), impls_vals.get(0).unwrap().as_slice()[0]);
    debug!("cat_did: {:?}", cat_did);
    debug!("cat_speak_did: {:?}", cat_speak_did);

    debug!("DOG DIDS");
    let (dog_did, dog_speak_did) =
        get_dids(tcx, impls_keys.get(1).unwrap(), impls_vals.get(1).unwrap().as_slice()[0]);
    debug!("dog_did: {:?}", dog_did);
    debug!("dog_speak_did: {:?}", dog_speak_did);

    // /////////////////////////

    // try: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.vtable_entries
    // - could potentially replace our get_cat() and get_dog() fakes
    //
    // _22 == &dyn Animal (arg to old dynamic speak() call)

    let cat_trait_ref = tcx.impl_trait_ref(impls_vals.get(0).unwrap().as_slice()[0]).unwrap().skip_binder();
    let dog_trait_ref = tcx.impl_trait_ref(impls_vals.get(1).unwrap().as_slice()[0]).unwrap().skip_binder();
    debug!("cat trait_ref: {:?}", cat_trait_ref);
    debug!("dog trait_ref: {:?}", dog_trait_ref);
    let cat_vtable_entries = tcx.vtable_entries(cat_trait_ref);
    let dog_vtable_entries = tcx.vtable_entries(dog_trait_ref);
    debug!("cat vtable_entries: {:?}", cat_vtable_entries);
    debug!("dog vtable_entries: {:?}", dog_vtable_entries);
    match cat_vtable_entries[3] {
        VtblEntry::Method(inst) => {
            debug!("inst.def: {:?}", inst.def);
            debug!("inst.args: {:?}", inst.args);
        }
        _ => debug!("another"),
    }

    // /////////////////////////

    // get old terminator's edges
    let edges = data.terminator().kind.edges();
    let bb_old_return;
    let bb_old_cleanup;
    match edges {
        TerminatorEdges::AssignOnReturn { return_, cleanup, .. } => {
            debug!("edges problems?");
            if return_.len() > 1 {
                debug!("RET: multiple return blocks");
            }
            if cleanup.is_none() {
                debug!("CLN: no cleanup");
            }
            bb_old_return = return_[0];
            bb_old_cleanup = cleanup.unwrap();
        }
        _ => {
            debug!("another TerminatorEdges");
            panic!("verifopt: need to set terminator edges");
        }
    }

    // /////////////////////////
    // add / modify blocks (+ add necessary locals)
    // /////////////////////////

    // TODO all added locals are mutable... is this important post-borrowck?
    // if so, how to make immut?

    // first local @ idx 9 (9 locals before pass)
    //
    // locals stack:
    // - _0: run() retval
    // - _1: num
    // - _2: animal
    // - _3: copy of _1 (usize)
    // - _4: _cat
    // - _5: _dog
    // - _6: speak() retval?
    // - _7: temp (first ptr::metadata block - the modified one)
    // - _8: copy _2 Transmute

    debug!("num_bbs: {:?}", num_bbs);
    let speak_ret_loc = add_emptytup_temp(tcx, patch);
    assert_eq!(speak_ret_loc.as_u32(), 9);

    let animal = Local::from_u32(2);
    let cat = Local::from_u32(4);
    let dog = Local::from_u32(5);

    // /////////////////////////
    // mod dyn dispatch block
    // /////////////////////////
    let dynmetadata_animal_loc = add_dynmetadata_temp(tcx, patch, traitobj_did);
    assert_eq!(dynmetadata_animal_loc.as_u32(), 10);
    let const_dyn_traitobj_loc = add_const_dyn_traitobj_temp(tcx, patch, ty);
    assert_eq!(const_dyn_traitobj_loc.as_u32(), 11);
    let bb_cat_ptr_metadata_exp = BasicBlock::from_usize(num_bbs);
    modify_dyndispatch_block(
        tcx,
        patch,
        traitobj_did,
        bb,
        data,
        bb_cat_ptr_metadata_exp,
        bb_old_cleanup,
        dynmetadata_animal_loc,
        const_dyn_traitobj_loc,
        Local::from_u32(7),
        Local::from_u32(6),
        Local::from_u32(8),
        Local::from_u32(7),
    );


    // /////////////////////////
    // TODO below


    // /////////////////////////
    // make cat block
    // /////////////////////////

    // /////////////////////////
    // coerce cat into dyn animal block
    // /////////////////////////

    // /////////////////////////
    // make dog block
    // /////////////////////////

    // /////////////////////////
    // coerce dog into dyn animal block
    // /////////////////////////


    // TODO above
    // /////////////////////////


    // /////////////////////////
    // ptr::metadata blocks
    // /////////////////////////

    // FIXME remove if can get vtable ptrs another way

    //struct PtrMetadataBlockLocals {
    //    dyn_traitobj: Local,
    //    const_dyn_traitobj_1: Local,
    //    const_dyn_traitobj_2: Local,
    //    dynmetadata: Local,
    //}

    // CAT

    let dyn_traitobj_cat_loc = add_dyn_traitobj_temp(tcx, patch, ty);
    let const_dyn_traitobj_cat_loc2 = add_const_dyn_traitobj_temp(tcx, patch, ty);
    let const_dyn_traitobj_cat_loc3 = add_const_dyn_traitobj_temp(tcx, patch, ty);
    let dynmetadata_cat_loc = add_dynmetadata_temp(tcx, patch, traitobj_did);
    assert_eq!(dynmetadata_cat_loc.as_u32(), 15);
    let bb_dog_ptr_metadata_exp = BasicBlock::from_usize(num_bbs + 1);
    let bb_cat_ptr_metadata_act = add_ptr_metadata_block(
        tcx,
        patch,
        bb_dog_ptr_metadata_exp,
        bb_old_cleanup,
        cat,
        dyn_traitobj_cat_loc,
        const_dyn_traitobj_cat_loc2,
        const_dyn_traitobj_cat_loc3,
        dynmetadata_cat_loc,
        traitobj_did,
        const_dyn_traitobj_loc,
    );
    assert_eq!(bb_cat_ptr_metadata_exp, bb_cat_ptr_metadata_act);

    // DOG

    let dyn_traitobj_dog_loc = add_dyn_traitobj_temp(tcx, patch, ty);
    let const_dyn_traitobj_dog_loc2 = add_const_dyn_traitobj_temp(tcx, patch, ty);
    let const_dyn_traitobj_dog_loc3 = add_const_dyn_traitobj_temp(tcx, patch, ty);
    let dynmetadata_dog_loc = add_dynmetadata_temp(tcx, patch, traitobj_did);
    assert_eq!(dynmetadata_dog_loc.as_u32(), 19);
    let bb_into_raw_exp = BasicBlock::from_usize(num_bbs + 2);
    let bb_dog_ptr_metadata_act = add_ptr_metadata_block(
        tcx,
        patch,
        bb_into_raw_exp,
        bb_old_cleanup,
        dog,
        dyn_traitobj_dog_loc,
        const_dyn_traitobj_dog_loc2,
        const_dyn_traitobj_dog_loc3,
        dynmetadata_dog_loc,
        traitobj_did,
        const_dyn_traitobj_loc,
    );
    assert_eq!(bb_dog_ptr_metadata_exp, bb_dog_ptr_metadata_act);

    // /////////////////////////
    // animal into_raw() block
    // /////////////////////////
    let mut_dyn_traitobj_loc = add_mut_dyn_traitobj_temp(tcx, patch, traitobj_did);
    let boxed_dyn_traitobj_loc1 = add_boxed_dyn_traitobj_temp(tcx, patch, traitobj_did);
    assert_eq!(boxed_dyn_traitobj_loc1.as_u32(), 21);
    let bb_first_compare_exp = BasicBlock::from_usize(num_bbs + 3);
    let bb_into_raw_act = add_into_raw_block(
        tcx,
        patch,
        bb_first_compare_exp,
        bb_old_cleanup,
        mut_dyn_traitobj_loc,
        boxed_dyn_traitobj_loc1,
        animal,
        traitobj_did,
        dyn_traitobj_cat_loc,
        const_dyn_traitobj_cat_loc2,
        const_dyn_traitobj_cat_loc3,
        const_dyn_traitobj_dog_loc2,
        const_dyn_traitobj_dog_loc3,
    );
    assert_eq!(bb_into_raw_exp, bb_into_raw_act);

    // /////////////////////////
    // compare animal w cat vtable address
    // /////////////////////////
    let raw_traitobj1_loc = add_raw_traitobj_temp(tcx, patch);
    let dynmetadata_animal_ref_loc = add_dynmetadata_ref_temp(tcx, patch, traitobj_did);
    let dynmetadata_cat_ref_loc = add_dynmetadata_ref_temp(tcx, patch, traitobj_did);
    let first_eq_res_loc = add_mut_bool_temp(tcx, patch);
    assert_eq!(first_eq_res_loc.as_u32(), 25);
    let bb_first_switch_exp = BasicBlock::from_usize(num_bbs + 4);
    let bb_first_compare_act = add_compare_vtable_block(
        tcx,
        patch,
        bb_first_switch_exp,
        bb_old_cleanup,
        raw_traitobj1_loc,
        mut_dyn_traitobj_loc,
        dynmetadata_animal_loc,
        dynmetadata_animal_ref_loc,
        dynmetadata_cat_loc,
        dynmetadata_cat_ref_loc,
        first_eq_res_loc,
        traitobj_did,
        false,
        boxed_dyn_traitobj_loc1,
    );
    assert_eq!(bb_first_compare_exp, bb_first_compare_act);

    // /////////////////////////
    // first switch statement
    // /////////////////////////
    let bb_second_compare_exp = BasicBlock::from_usize(num_bbs + 7);
    let bb_cat_speak_exp = BasicBlock::from_usize(num_bbs + 5);
    let bb_first_switch_act =
        add_switch_block(tcx, patch, bb_cat_speak_exp, bb_second_compare_exp, first_eq_res_loc);
    assert_eq!(bb_first_switch_exp, bb_first_switch_act);

    // /////////////////////////
    // cat speak block
    // /////////////////////////
    let raw_traitobj2_loc = add_raw_traitobj_temp(tcx, patch);
    let cat_loc = add_concretety_ref_temp(tcx, patch, cat_did);
    assert_eq!(cat_loc.as_u32(), 27);
    let bb_cat_goto_exp = BasicBlock::from_usize(num_bbs + 6);
    let bb_cat_speak_act = add_speak_block(
        tcx,
        patch,
        bb_cat_goto_exp,
        bb_old_cleanup,
        raw_traitobj1_loc,
        raw_traitobj2_loc,
        speak_ret_loc,
        cat_loc,
        cat_did,
        cat_speak_did,
        raw_traitobj1_loc,
        dynmetadata_animal_ref_loc,
        dynmetadata_cat_ref_loc,
        first_eq_res_loc,
    );
    assert_eq!(bb_cat_speak_exp, bb_cat_speak_act);

    // /////////////////////////
    // cat goto block
    // /////////////////////////
    let bb_cat_goto_act = add_goto_block(patch, bb_old_return, cat_loc, speak_ret_loc);
    assert_eq!(bb_cat_goto_exp, bb_cat_goto_act);

    // /////////////////////////
    // compare animal w dog vtable address
    // /////////////////////////
    let raw_traitobj3_loc = add_raw_traitobj_temp(tcx, patch);
    let dynmetadata_dog_ref_loc = add_dynmetadata_ref_temp(tcx, patch, traitobj_did);
    let second_eq_res_loc = add_mut_bool_temp(tcx, patch);
    assert_eq!(second_eq_res_loc.as_u32(), 30);
    let bb_second_switch_exp = BasicBlock::from_usize(num_bbs + 8);
    let bb_second_compare_act = add_compare_vtable_block(
        tcx,
        patch,
        bb_second_switch_exp,
        bb_old_cleanup,
        raw_traitobj3_loc,
        mut_dyn_traitobj_loc,
        dynmetadata_animal_loc,
        dynmetadata_animal_ref_loc,
        dynmetadata_dog_loc,
        dynmetadata_dog_ref_loc,
        second_eq_res_loc,
        traitobj_did,
        true,
        boxed_dyn_traitobj_loc1,
    );
    assert_eq!(bb_second_compare_exp, bb_second_compare_act);

    // /////////////////////////
    // second switch statement
    // /////////////////////////
    let bb_dog_speak_exp = BasicBlock::from_usize(num_bbs + 9);
    let bb_second_switch_act =
        add_switch_block(tcx, patch, bb_dog_speak_exp, bb_old_return, second_eq_res_loc);
    assert_eq!(bb_second_switch_exp, bb_second_switch_act);

    // /////////////////////////
    // dog speak block
    // /////////////////////////
    let raw_traitobj4_loc = add_raw_traitobj_temp(tcx, patch);
    let dog_loc = add_concretety_ref_temp(tcx, patch, dog_did);
    assert_eq!(dog_loc.as_u32(), 32);
    let bb_dog_goto_exp = BasicBlock::from_usize(num_bbs + 10);
    let bb_dog_speak_act = add_speak_block(
        tcx,
        patch,
        bb_dog_goto_exp,
        bb_old_cleanup,
        raw_traitobj1_loc,
        raw_traitobj4_loc,
        speak_ret_loc,
        dog_loc,
        dog_did,
        dog_speak_did,
        raw_traitobj1_loc,
        dynmetadata_animal_ref_loc,
        dynmetadata_dog_ref_loc,
        second_eq_res_loc,
    );
    assert_eq!(bb_dog_speak_exp, bb_dog_speak_act);

    // /////////////////////////
    // dog goto block
    // /////////////////////////
    let bb_dog_goto_act = add_goto_block(patch, bb_old_return, dog_loc, speak_ret_loc);
    assert_eq!(bb_dog_goto_exp, bb_dog_goto_act);

    // /////////////////////////
    // TODO make sure cleanup funnels to the same place
    // /////////////////////////
}

fn dummy_span() -> Span {
    Span::new(BytePos(0), BytePos(0), SyntaxContext::root(), None)
}

fn dummy_source_info() -> SourceInfo {
    SourceInfo {
        span: dummy_span(),
        // FIXME use for scoping!
        scope: SourceScope::ZERO,
    }
}

fn make_empty_tup<'tcx>(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    let tup_inner: &[Ty<'tcx>] = &[];
    Ty::new_tup(tcx, tup_inner)
}

/*
 * let _: &dyn Animal;
 */
fn add_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    ty: Ty<'tcx>,
) -> Local {
    // get dyn Animal
    let dyn_traitobj = ty.clone();

    // add &dyn Animal local to patch
    patch.new_temp(
        Ty::new_ref(
            tcx,
            Region::new_from_kind(tcx, RegionKind::ReErased),
            dyn_traitobj,
            Mutability::Not,
        ),
        dummy_span(),
    )
}

/*
 * let mut: *const dyn Animal;
 */
fn add_const_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    ty: Ty<'tcx>,
) -> Local {
    // get dyn Animal
    let dyn_traitobj = ty.clone();

    // add *const dyn Animal local to patch
    patch.new_temp(Ty::new_imm_ptr(tcx, dyn_traitobj), dummy_span())
}

#[allow(rustc::usage_of_ty_tykind)]
fn make_dyn_traitobj_tykind<'tcx>(tcx: TyCtxt<'tcx>, traitobj_did: DefId) -> TyKind<'tcx> {
    // construct args list (containing dyn Animal)
    let dummy_args: Vec<GenericArg<'tcx>> = Vec::new();
    let pep_list = tcx.mk_poly_existential_predicates(&[Binder::dummy(
        ExistentialPredicate::Trait(ExistentialTraitRef::new(tcx, traitobj_did, dummy_args)),
    )]);

    Dynamic(pep_list, Region::new_from_kind(tcx, RegionKind::ReErased))
}

fn make_dynmetadata_adt<'tcx>(tcx: TyCtxt<'tcx>, traitobj_did: DefId) -> Ty<'tcx> {
    // DynMetadata AdtDef
    let dynmetadata_adt_def = tcx.adt_def(tcx.lang_items().dyn_metadata().unwrap());

    // GenArgsRef
    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(dyn_traitobj_ty)]);

    Ty::new_adt(tcx, dynmetadata_adt_def, gen_args_ref)
}

/*
 * let _: std:ptr::DynMetadata<dyn Animal>;
 */
fn add_dynmetadata_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
) -> Local {
    let dm_adt = make_dynmetadata_adt(tcx, traitobj_did);
    patch.new_temp(dm_adt, dummy_span())
}

/*
 * let mut _: &std:ptr::DynMetadata<dyn Animal>;
 */
fn add_dynmetadata_ref_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
) -> Local {
    // add &DynMetadata local to patch
    let dm_adt = make_dynmetadata_adt(tcx, traitobj_did);
    patch.new_temp(
        Ty::new_ref(tcx, Region::new_from_kind(tcx, RegionKind::ReErased), dm_adt, Mutability::Not),
        dummy_span(),
    )
}

/*
 * let mut _: *const ();
 */
fn add_raw_traitobj_temp<'tcx>(tcx: TyCtxt<'tcx>, patch: &mut MirPatch<'tcx>) -> Local {
    patch.new_temp(Ty::new_imm_ptr(tcx, make_empty_tup(tcx)), dummy_span())
}

/*
 * let mut _: *mut dyn Animal;
 */
fn add_mut_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
) -> Local {
    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);
    patch.new_temp(Ty::new_mut_ptr(tcx, dyn_traitobj_ty), dummy_span())
}

/*
 * let mut _: std::boxed::Box<dyn Animal>;
 */
fn add_boxed_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
) -> Local {
    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);
    let boxed_dyn_traitobj_ty = Ty::new_box(tcx, dyn_traitobj_ty);
    patch.new_temp(boxed_dyn_traitobj_ty, dummy_span())
}

/*
 * let _: ();
 */
fn add_emptytup_temp<'tcx>(tcx: TyCtxt<'tcx>, patch: &mut MirPatch<'tcx>) -> Local {
    patch.new_temp(make_empty_tup(tcx), dummy_span())
}

/*
 * let _: &Cat;
 * or
 * let _: &Dog;
 */
fn add_concretety_ref_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    cat_did: DefId,
) -> Local {
    let cat_adt_def = tcx.adt_def(cat_did);
    let gen_args: &[GenericArg<'tcx>] = &[];
    let gen_args_ref = tcx.mk_args(gen_args);
    patch.new_temp(
        Ty::new_ref(
            tcx,
            Region::new_from_kind(tcx, RegionKind::ReErased),
            Ty::new_adt(tcx, cat_adt_def, gen_args_ref),
            Mutability::Not,
        ),
        dummy_span(),
    )
}

/*
 * let mut _: bool;
 */
fn add_mut_bool_temp<'tcx>(tcx: TyCtxt<'tcx>, patch: &mut MirPatch<'tcx>) -> Local {
    patch.new_temp(tcx.mk_ty_from_kind(crate::ty::Bool), dummy_span())
}

fn add_goto_block<'tcx>(
    patch: &mut MirPatch<'tcx>,
    bb_return: BasicBlock,
    free1: Local,
    free2: Local,
) -> BasicBlock {
    let mut stmts = Vec::new();
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free1)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free2)));

    // construct terminator
    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Goto { target: bb_return },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    // if statements, use BBD::new_stmts()
    patch.new_block(bb_data)
}

fn add_speak_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_goto: BasicBlock,
    bb_cleanup: BasicBlock,
    raw_traitobj1_loc: Local,
    raw_traitobj2_loc: Local,
    func_ret_loc: Local,
    concrete_ty_loc: Local,
    concrete_ty_did: DefId,
    speak_fn_did: DefId,
    free1: Local,
    free2: Local,
    free3: Local,
    free4: Local,
) -> BasicBlock {
    // /////////////////////////
    // [og place] = [rw place] (n == new local)
    //  = _30 (*const ()) - (raw_animal)
    //  = _38 (*const ()) - (cp _30)
    //  = _37 (&Cat) - (Transmute _38 -> &Cat)
    //  = _36 (&Cat) - (==_37)
    //  = _40 (&Cat) - (==_37)
    //  = _39 (()) - (speak result)
    //
    // add block (cat speak):
    // - copy
    // - Transmute
    // - &*
    // - &*
    // - speak
    // /////////////////////////

    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);
    let mut stmts = Vec::new();

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free1)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free2)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free3)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free4)));

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(raw_traitobj2_loc)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(concrete_ty_loc)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(func_ret_loc)));

    // copy raw_animal ptr
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: raw_traitobj2_loc, projection: empty_proj },
            Rvalue::Use(Operand::Copy(Place { local: raw_traitobj1_loc, projection: empty_proj })),
        ))),
    ));

    // transmute raw_animal copy into &concrete_ty
    let cat_adt_def = tcx.adt_def(concrete_ty_did);
    let gen_args: &[GenericArg<'tcx>] = &[];
    let gen_args_ref = tcx.mk_args(gen_args);

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: concrete_ty_loc, projection: empty_proj },
            Rvalue::Cast(
                CastKind::Transmute,
                Operand::Move(Place { local: raw_traitobj2_loc, projection: empty_proj }),
                Ty::new_ref(
                    tcx,
                    Region::new_from_kind(tcx, RegionKind::ReErased),
                    Ty::new_adt(tcx, cat_adt_def, gen_args_ref),
                    Mutability::Not,
                ),
            ),
        ))),
    ));

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(raw_traitobj1_loc)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(raw_traitobj2_loc)));

    // why &*s? try just using result of prev as speak arg

    // construct Cat::speak call
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: concrete_ty_loc, projection: empty_proj }),
        span: dummy_span(),
    }]);

    let gen_args: &[GenericArg<'tcx>] = &[];
    let gen_args_ref = tcx.mk_args(gen_args);

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Call {
            func: Operand::Constant(Box::new(ConstOperand {
                span: dummy_span(),
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    ConstValue::ZeroSized,
                    Ty::new_fn_def(tcx, speak_fn_did, gen_args_ref),
                ),
            })),
            args,
            destination: Place { local: func_ret_loc, projection: empty_proj },
            target: Some(bb_goto),
            unwind: UnwindAction::Cleanup(bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    patch.new_block(bb_data)
}

fn add_switch_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_eq: BasicBlock,
    bb_neq: BasicBlock,
    eq_res_loc: Local,
) -> BasicBlock {
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let targets = vec![(0u128, bb_neq)].into_iter();

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Move(Place { local: eq_res_loc, projection: empty_proj }),
            targets: SwitchTargets::new(targets, bb_eq),
        },
    };

    let bb_data = BasicBlockData::new(Some(term), false);
    patch.new_block(bb_data)
}

fn add_compare_vtable_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_first_switch: BasicBlock,
    bb_cleanup: BasicBlock,
    raw_traitobj1_loc: Local,
    mut_dyn_traitobj_loc: Local,
    dynmetadata_traitobj_loc: Local,
    dynmetadata_traitobj_ref_loc: Local,
    dynmetadata_concretety_loc: Local,
    dynmetadata_concretety_ref_loc: Local,
    eq_res_loc: Local,
    traitobj_did: DefId,
    done_copy: bool,
    free1: Local,
) -> BasicBlock {
    // /////////////////////////
    // add block (first compare):
    // - (PtrToPtr)
    // - ref of prev dynmetadata res (_26n/_21) (for animal)
    // - ref of prev dynmetadata res (?/_24) (for cat)
    // - Eq
    // /////////////////////////
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free1)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(raw_traitobj1_loc)));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: raw_traitobj1_loc, projection: empty_proj },
            Rvalue::Cast(
                CastKind::PtrToPtr,
                Operand::Move(Place { local: mut_dyn_traitobj_loc, projection: empty_proj }),
                Ty::new_imm_ptr(tcx, make_empty_tup(tcx)),
            ),
        ))),
    ));

    debug!("DONE_COPY: {:?}", done_copy);
    if done_copy {
        stmts.push(Statement::new(
            dummy_source_info(),
            StatementKind::StorageDead(mut_dyn_traitobj_loc),
        ));
    }
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(dynmetadata_traitobj_ref_loc),
    ));
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(dynmetadata_concretety_ref_loc),
    ));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(eq_res_loc)));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: dynmetadata_traitobj_ref_loc, projection: empty_proj },
            Rvalue::Ref(
                Region::new_from_kind(tcx, RegionKind::ReErased),
                rustc_middle::mir::BorrowKind::Shared,
                Place { local: dynmetadata_traitobj_loc, projection: empty_proj },
            ),
        ))),
    ));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: dynmetadata_concretety_ref_loc, projection: empty_proj },
            Rvalue::Ref(
                Region::new_from_kind(tcx, RegionKind::ReErased),
                rustc_middle::mir::BorrowKind::Shared,
                Place { local: dynmetadata_concretety_loc, projection: empty_proj },
            ),
        ))),
    ));

    // add terminator
    let dm_adt = make_dynmetadata_adt(tcx, traitobj_did);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(dm_adt), GenericArg::from(dm_adt)]);

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([
        Spanned {
            node: Operand::Move(Place {
                local: dynmetadata_traitobj_ref_loc,
                projection: empty_proj,
            }),
            span: dummy_span(),
        },
        Spanned {
            node: Operand::Move(Place {
                local: dynmetadata_concretety_ref_loc,
                projection: empty_proj,
            }),
            span: dummy_span(),
        },
    ]);

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Call {
            func: Operand::Constant(Box::new(ConstOperand {
                span: dummy_span(),
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    ConstValue::ZeroSized,
                    Ty::new_fn_def(
                        tcx,
                        DefId { index: DefIndex::from_u32(3219), krate: CrateNum::from_u32(2) },
                        gen_args_ref,
                    ),
                ),
            })),
            args,
            destination: Place { local: eq_res_loc, projection: empty_proj },
            target: Some(bb_first_switch),
            unwind: UnwindAction::Cleanup(bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    patch.new_block(bb_data)
}

fn add_into_raw_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_first_switch: BasicBlock,
    bb_cleanup: BasicBlock,
    mut_dyn_traitobj_loc: Local,
    boxed_dyn_traitobj_loc: Local,
    boxed_dyn_traitobj_animal_loc: Local,
    traitobj_did: DefId,
    free1: Local,
    free2: Local,
    free3: Local,
    free4: Local,
    free5: Local,
) -> BasicBlock {
    // /////////////////////////
    // add block (animal into_raw):
    // - const false (?)
    // - move
    // - into_raw
    // /////////////////////////
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free1)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free2)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free3)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free4)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free5)));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(mut_dyn_traitobj_loc),
    ));
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(boxed_dyn_traitobj_loc),
    ));
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(boxed_dyn_traitobj_animal_loc),
    ));

    // TODO const false ?

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: boxed_dyn_traitobj_loc, projection: empty_proj },
            Rvalue::Use(Operand::Move(Place {
                local: boxed_dyn_traitobj_animal_loc,
                projection: empty_proj,
            })),
        ))),
    ));

    // add terminator
    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);
    let boxed_dyn_traitobj_ty = Ty::new_box(tcx, dyn_traitobj_ty);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(boxed_dyn_traitobj_ty)]);

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: boxed_dyn_traitobj_loc, projection: empty_proj }),
        span: dummy_span(),
    }]);

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Call {
            func: Operand::Constant(Box::new(ConstOperand {
                span: dummy_span(),
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    ConstValue::ZeroSized,
                    Ty::new_fn_def(
                        tcx,
                        DefId { index: DefIndex::from_u32(730), krate: CrateNum::from_u32(3) },
                        gen_args_ref,
                    ),
                ),
            })),
            args,
            destination: Place { local: mut_dyn_traitobj_loc, projection: empty_proj },
            target: Some(bb_first_switch),
            unwind: UnwindAction::Cleanup(bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    patch.new_block(bb_data)
}

fn add_ptr_metadata_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_next: BasicBlock,
    bb_cleanup: BasicBlock,
    boxed_dyn_traitobj_loc: Local,
    dyn_traitobj_loc: Local,
    const_dyn_traitobj_loc1: Local,
    const_dyn_traitobj_loc2: Local,
    dynmetadata_loc: Local,
    traitobj_did: DefId,
    free1: Local,
) -> BasicBlock {
    // /////////////////////////
    // add ptr_metadata block:
    // - copy std::ptr::Unique<dyn Animal>.0: std::ptr::NonNull<dyn Animal>) as *const dyn Animal (Transmute);
    // - &*
    // - &raw const
    // - ptr_metadata call
    // /////////////////////////

    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);

    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let deref_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[ProjectionElem::Deref];
    let deref_proj = tcx.mk_place_elems(deref_proj_slice);

    let unique_adt_def =
        tcx.adt_def(DefId { index: DefIndex::from_u32(2677), krate: CrateNum::from_u32(2) });
    let nonnull_adt_def =
        tcx.adt_def(DefId { index: DefIndex::from_u32(2532), krate: CrateNum::from_u32(2) });
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(dyn_traitobj_ty)]);
    let fields_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[
        ProjectionElem::Field(
            FieldIdx::from_u32(0),
            Ty::new_adt(tcx, unique_adt_def, gen_args_ref),
        ),
        ProjectionElem::Field(
            FieldIdx::from_u32(0),
            Ty::new_adt(tcx, nonnull_adt_def, gen_args_ref),
        ),
    ];
    let fields_proj = tcx.mk_place_elems(fields_proj_slice);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(free1)));

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(dyn_traitobj_loc)));
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(const_dyn_traitobj_loc1),
    ));
    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::StorageLive(const_dyn_traitobj_loc2),
    ));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(dynmetadata_loc)));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: const_dyn_traitobj_loc1, projection: empty_proj },
            Rvalue::Cast(
                CastKind::Transmute,
                Operand::Copy(Place { local: boxed_dyn_traitobj_loc, projection: fields_proj }),
                Ty::new_ptr(tcx, dyn_traitobj_ty, Mutability::Not),
            ),
        ))),
    ));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: dyn_traitobj_loc, projection: empty_proj },
            Rvalue::Ref(
                Region::new_from_kind(tcx, RegionKind::ReErased),
                rustc_middle::mir::BorrowKind::Shared,
                Place { local: const_dyn_traitobj_loc1, projection: deref_proj },
            ),
        ))),
    ));

    stmts.push(Statement::new(
        dummy_source_info(),
        StatementKind::Assign(Box::new((
            Place { local: const_dyn_traitobj_loc2, projection: empty_proj },
            Rvalue::RawPtr(
                RawPtrKind::Const,
                Place { local: dyn_traitobj_loc, projection: deref_proj },
            ),
        ))),
    ));

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: const_dyn_traitobj_loc2, projection: empty_proj }),
        span: dummy_span(),
    }]);

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Call {
            func: Operand::Constant(Box::new(ConstOperand {
                span: dummy_span(),
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    ConstValue::ZeroSized,
                    Ty::new_fn_def(
                        tcx,
                        DefId { index: DefIndex::from_u32(2452), krate: CrateNum::from_u32(2) },
                        gen_args_ref,
                    ),
                ),
            })),
            args,
            destination: Place { local: dynmetadata_loc, projection: empty_proj },
            target: Some(bb_next),
            unwind: UnwindAction::Cleanup(bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    patch.new_block(bb_data)
}

fn modify_dyndispatch_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
    bb: BasicBlock,
    data: &BasicBlockData<'tcx>,
    bb_next: BasicBlock,
    bb_cleanup: BasicBlock,
    dynmetadata_loc: Local,
    const_dyn_traitobj_loc: Local,
    dyn_traitobj_loc: Local,
    free1: Local,
    free2: Local,
    free3: Local,
) {
    let (num_statements, first_non_storage_idx, locals_to_liven) = get_relevant_indices(data);

    add_raw_const_stmt(tcx, patch, bb, num_statements, const_dyn_traitobj_loc, dyn_traitobj_loc);

    replace_term_ptrmetadata_call(
        tcx,
        patch,
        traitobj_did,
        bb,
        bb_next,
        bb_cleanup,
        dynmetadata_loc,
        const_dyn_traitobj_loc,
    );

    patch.add_statement(
        Location { block: bb, statement_index: first_non_storage_idx },
        StatementKind::StorageDead(free1),
    );

    for loc in locals_to_liven.iter() {
        patch.add_statement(
            Location { block: bb, statement_index: first_non_storage_idx },
            StatementKind::StorageLive(*loc),
        );
    }

    patch.add_statement(
        Location { block: bb, statement_index: first_non_storage_idx },
        StatementKind::StorageLive(dynmetadata_loc),
    );
    patch.add_statement(
        Location { block: bb, statement_index: first_non_storage_idx },
        StatementKind::StorageLive(const_dyn_traitobj_loc),
    );

    patch.add_statement(
        Location { block: bb, statement_index: num_statements },
        StatementKind::StorageDead(free2),
    );
    patch.add_statement(
        Location { block: bb, statement_index: num_statements },
        StatementKind::StorageDead(free3),
    );
}

fn get_relevant_indices<'tcx>(data: &BasicBlockData<'tcx>) -> (usize, usize, Vec<Local>) {
    // iterate through block statements to get:
    // - [x] place indices (locals)
    // - [x] statement indices
    debug!("MOD FIRST BLOCK");
    let num_statements = data.statements.len();
    debug!("num_statements: {:?}", num_statements);
    let mut first_non_storage_idx = 0;

    // get statement indices
    let mut locals_alive = vec![];
    for (idx, stmt) in data.statements.iter().enumerate() {
        match &stmt.kind {
            StatementKind::StorageDead(_) => continue,
            StatementKind::StorageLive(loc) => {
                locals_alive.push(loc);
                continue;
            }
            _ => {
                first_non_storage_idx = idx;
                break;
            }
        }
    }
    // get place indices
    debug!("TO LIVEN");
    let mut locals_to_liven = vec![];
    for stmt in data.statements.iter() {
        match &stmt.kind {
            StatementKind::Assign(boxed) => {
                let (lplace, _rval) = *(boxed.clone());
                debug!("lplace: {:?}", lplace.local.as_u32());
                locals_to_liven.push(lplace.local);
            }
            _ => {}
        }
    }

    // only enliven non-live locals
    locals_to_liven.retain(|loc| !locals_alive.contains(&loc));
    debug!("locals_to_liven: {:?}", locals_to_liven);

    (num_statements, first_non_storage_idx, locals_to_liven)
}

fn add_raw_const_stmt<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb: BasicBlock,
    idx: usize,
    const_dyn_traitobj_loc: Local,
    dyn_traitobj_loc: Local,
) {
    let loc = Location { block: bb, statement_index: idx };

    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let deref_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[ProjectionElem::Deref];
    let deref_proj = tcx.mk_place_elems(deref_proj_slice);

    patch.add_assign(
        loc,
        Place { local: const_dyn_traitobj_loc, projection: empty_proj },
        Rvalue::RawPtr(
            RawPtrKind::Const,
            Place { local: dyn_traitobj_loc, projection: deref_proj },
        ),
    );
}

fn replace_term_ptrmetadata_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    traitobj_did: DefId,
    bb: BasicBlock,
    bb_next: BasicBlock,
    bb_cleanup: BasicBlock,
    dynmetadata_loc: Local,
    const_dyn_traitobj_loc: Local,
) {
    // make empty projection
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let dyn_traitobj_tykind = make_dyn_traitobj_tykind(tcx, traitobj_did);
    let dyn_traitobj_ty = tcx.mk_ty_from_kind(dyn_traitobj_tykind);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(dyn_traitobj_ty)]);

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: const_dyn_traitobj_loc, projection: empty_proj }),
        span: dummy_span(),
    }]);

    patch.patch_terminator(
        bb,
        TerminatorKind::Call {
            func: Operand::Constant(Box::new(ConstOperand {
                span: dummy_span(),
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    ConstValue::ZeroSized,
                    Ty::new_fn_def(
                        tcx,
                        DefId { index: DefIndex::from_u32(2452), krate: CrateNum::from_u32(2) },
                        gen_args_ref,
                    ),
                ),
            })),
            args,
            destination: Place { local: dynmetadata_loc, projection: empty_proj },
            target: Some(bb_next),
            unwind: UnwindAction::Cleanup(bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    );
}

// Identification helpers

fn id_ty<'tcx>(ty: Ty<'tcx>) {
    debug!("-TyKind:");
    match ty.kind() {
        crate::ty::Bool => debug!("Bool"),
        crate::ty::Char => debug!("Char"),
        crate::ty::Int(_) => debug!("Int"),
        crate::ty::Uint(_) => debug!("Uint"),
        crate::ty::Float(_) => debug!("Float"),
        crate::ty::Adt(def, rawlist) => {
            debug!("Adt");
            debug!("def: {:?}", def);
            let did = def.did();
            debug!("did.index: {:?}", did.index);
            debug!("did.krate: {:?}", did.krate);
            debug!("def.kind(): {:?}", def.adt_kind());
            debug!("def.repr(): {:?}", def.repr());
            debug!("rawlist: {:?}", rawlist);
            debug!("genargs...");
            for (gidx, genarg) in rawlist.iter().enumerate() {
                debug!("--GENARGSidx: {:?}", gidx);
                let type_opt = genarg.as_type();
                debug!("kind: {:?}", genarg.kind());
                debug!("as_region: {:?}", genarg.as_region());
                debug!("as_type: {:?}", type_opt);
                debug!("as_const: {:?}", genarg.as_const());
                if type_opt.is_some() {
                    id_ty(type_opt.unwrap());
                }
            }
            id_adt_variants(*def);
        }
        crate::ty::Foreign(_) => debug!("Foreign"),
        crate::ty::Str => debug!("Str"),
        crate::ty::Array(..) => debug!("Array"),
        crate::ty::Pat(..) => debug!("Pat"),
        crate::ty::Slice(..) => debug!("Slice"),
        crate::ty::RawPtr(ty, m) => {
            debug!("RawPtr");
            debug!("mut: {:?}", m);
            debug!("inner ty: {:?}", ty);
            id_ty(*ty);
        }
        crate::ty::Ref(reg, ty, m) => {
            debug!("Ref");
            debug!("region kind: {:?}", reg.kind());
            debug!("ty: {:?}", ty);
            id_ty(*ty);
            debug!("mut: {:?}", m);
        }
        crate::ty::FnDef(..) => debug!("FnDef"),
        crate::ty::FnPtr(..) => debug!("FnPtr"),
        crate::ty::UnsafeBinder(..) => debug!("UnsafeBinder"),
        crate::ty::Dynamic(rawlist, region) => {
            debug!("Dynamic");
            debug!("region: {:?}", region.kind());
            debug!("rawlist...");
            for (i, binder) in rawlist.iter().enumerate() {
                debug!("--idx: {:?}", i);
                if let Some(ty) = binder.no_bound_vars() {
                    match ty {
                        ExistentialPredicate::Trait(etr) => {
                            debug!("Trait");
                            debug!("etr.def_id: {:?}", etr.def_id);
                            debug!("etr.args: {:?}", etr.args);
                            debug!("did index?: {:?}", etr.def_id.index);
                            debug!("did krate?: {:?}", etr.def_id.krate);
                        }
                        _ => {}
                    }
                }
            }
        }
        crate::ty::Closure(..) => debug!("Closure"),
        crate::ty::CoroutineClosure(..) => debug!("CoroutineClosure"),
        crate::ty::Coroutine(..) => debug!("Coroutine"),
        crate::ty::CoroutineWitness(..) => debug!("CoroutineWitness"),
        crate::ty::Never => debug!("Never"),
        crate::ty::Tuple(rawlist) => {
            debug!("Tuple");
            debug!("rawlist...");
            for (i, ty) in rawlist.iter().enumerate() {
                debug!("i: {:?}", i);
                id_ty(ty);
            }
        }
        crate::ty::Alias(..) => debug!("Alias"),
        crate::ty::Param(..) => debug!("Param"),
        crate::ty::Bound(..) => debug!("Bound"),
        crate::ty::Placeholder(..) => debug!("Placeholder"),
        crate::ty::Infer(..) => debug!("Infer"),
        crate::ty::Error(..) => debug!("Error"),
    }
}

fn id_adt_variants<'tcx>(def: AdtDef<'tcx>) {
    debug!("variants...");
    for (vidx, variant) in def.variants().into_iter().enumerate() {
        debug!("--VARIANTidx: {:?}", vidx);
        debug!("variant: {:?}", variant);
        debug!("name: {:?}", variant.name.as_u32());
        for (fidx, field) in variant.fields.iter().enumerate() {
            debug!("---FIELDidx: {:?}", fidx);
            debug!("field: {:?}", field);
            debug!("name: {:?}", field.name.as_u32());
            debug!("visibility: {:?}", field.vis);
            match field.vis {
                Visibility::Restricted(id) => {
                    debug!("restricted id: {:?}", id);
                    debug!("id.index: {:?}", id.index);
                    debug!("id.krate: {:?}", id.krate);
                }
                _ => {}
            }
        }
    }
}

fn id_place<'tcx>(place: Place<'tcx>) {
    debug!("place.local: {:?}", place.local);
    debug!("place.proj: {:?}", place.projection);
    debug!("PLACE PROJECTIONS");
    for (idx, (place_ref, place_elem)) in place.iter_projections().enumerate() {
        debug!("START -{:?}", idx);
        debug!("OUTER REF");
        id_place_ref(place_ref);
        debug!("OUTER ELEM");
        id_place_elem(place_elem);
        debug!("END -{:?}", idx);
    }
    debug!("END ID_PLACE");
}

fn id_place_ref<'tcx>(place_ref: PlaceRef<'tcx>) {
    debug!("place_ref: {:?}", place_ref);
    debug!("place_ref.local: {:?}", place_ref.local);
    debug!("place_ref.projections: {:?}", place_ref.projection);
    debug!("PLACE REF PROJECTIONS");
    for (idx, (place_ref_inner, place_elem_inner)) in place_ref.iter_projections().enumerate() {
        debug!("START -{:?}", idx);
        debug!("INNER ref");
        id_place_ref(place_ref_inner);
        debug!("INNER elem");
        id_place_elem(place_elem_inner);
        debug!("END -{:?}", idx);
    }
    debug!("END ID_PLACE_REF");
}

fn id_place_elem<'tcx>(place_elem: PlaceElem<'tcx>) {
    debug!("place_elem: {:?}", place_elem);
    debug!("PlaceElem Variant");
    match place_elem {
        crate::ProjectionElem::Field(idx, ty) => {
            debug!("Field");
            debug!("idx: {:?}", idx);
            id_ty(ty);
        }
        _ => debug!("another"),
    }
}

fn id_stmt<'tcx>(kind: &StatementKind<'tcx>) {
    debug!("--StatementKind:");
    match kind {
        StatementKind::Assign(boxed_assign) => {
            debug!("Assign");
            let (_place, rvalue) = *boxed_assign.clone();
            match rvalue {
                Rvalue::Use(op) => {
                    debug!("RValue Kind: Use");
                    match op {
                        Operand::Copy(_) => debug!("Copy"),
                        Operand::Move(_) => debug!("Move"),
                        Operand::Constant(_) => debug!("Constant"),
                    }
                }
                Rvalue::BinaryOp(binop, boxed_ops) => {
                    debug!("RValue Kind: BinaryOp");
                    match binop {
                        BinOp::Eq => debug!("Binop: Eq"),
                        _ => debug!("Binop: another"),
                    }
                    let (op1, op2) = *boxed_ops;
                    match op1 {
                        Operand::Copy(_) => debug!("Copy"),
                        Operand::Move(_) => debug!("Move"),
                        Operand::Constant(_) => debug!("Constant"),
                    }
                    match op2 {
                        Operand::Copy(_) => debug!("Copy"),
                        Operand::Move(_) => debug!("Move"),
                        Operand::Constant(_) => debug!("Constant"),
                    }
                }
                Rvalue::Ref(region, borrowkind, _place) => {
                    debug!("RValue Kind: Ref");
                    match region.kind() {
                        RegionKind::ReErased => debug!("RegionKind: ReErased"),
                        _ => debug!("RegionKind: another"),
                    }
                    match borrowkind {
                        rustc_middle::mir::BorrowKind::Shared => debug!("BorrowKind: Shared"),
                        _ => debug!("BorrowKind: another"),
                    }
                }
                Rvalue::Cast(castkind, op, ty) => {
                    debug!("RValue Kind: Cast");
                    match castkind {
                        CastKind::PtrToPtr => debug!("CastKind: PtrToPtr"),
                        CastKind::Transmute => debug!("CastKind: Transmute"),
                        _ => debug!("CastKind: another"),
                    }
                    match op {
                        Operand::Copy(place) => {
                            debug!("Copy");
                            id_place(place);
                        }
                        Operand::Move(place) => {
                            debug!("Move");
                            id_place(place);
                        }
                        Operand::Constant(_) => {
                            debug!("Constant");
                        }
                    }
                    debug!("Ty: {:?}", ty);
                    id_ty(ty);
                }
                Rvalue::RawPtr(rawptrkind, place) => {
                    debug!("RValue Kind: RawPtr");
                    debug!("RawPtrKind::{:?}", rawptrkind);
                    id_place(place);
                }
                _ => debug!("RValue Kind: another"),
            }
        }
        StatementKind::StorageLive(..) => debug!("StorageLive"),
        StatementKind::StorageDead(..) => debug!("StorageDead"),
        _ => debug!("another"),
    }
}

fn id_term<'tcx>(tcx: TyCtxt<'tcx>, kind: &TerminatorKind<'tcx>) {
    debug!("--TerminatorKind:");
    match kind {
        TerminatorKind::Call {
            func: operand,
            args: op_args,
            destination: dst,
            target: bb_opt,
            unwind: unwind_act,
            call_source: callsource,
            fn_span: span,
        } => {
            debug!("Call");
            debug!("func: {:?}", operand);
            match operand {
                Operand::Copy(_) => debug!("Copy"),
                Operand::Move(_) => debug!("Move"),
                Operand::Constant(const_op) => {
                    debug!("Constant: {:?}", const_op);
                    debug!("span: {:?}", (*const_op).span);
                    debug!("user_ty: {:?}", (*const_op).user_ty);
                    match (*const_op).const_ {
                        rustc_middle::mir::Const::Ty(ty, c) => {
                            debug!("Const::Ty");
                            debug!("ty: {:?}", ty);
                            debug!("const: {:?}", c);
                        }
                        rustc_middle::mir::Const::Unevaluated(uneval_const, ty) => {
                            debug!("Const::Unevaluated");
                            debug!("UnevaluatedConst: {:?}", uneval_const);
                            debug!("Ty: {:?}", ty);
                        }
                        rustc_middle::mir::Const::Val(const_val, ty) => {
                            debug!("Const::Val");
                            debug!("ConstValue: {:?}", const_val);
                            debug!("Ty: {:?}", ty);
                            match ty.kind() {
                                crate::ty::FnDef(defid, rawlist) => {
                                    debug!("defid.index: {:?}", defid.index);
                                    debug!("defid.krate: {:?}", defid.krate);
                                    debug!("rawlist: {:?}", rawlist);
                                    // TODO check expected type of
                                    // first parameter here (_not_ the
                                    // arg, which may happen to be dyn,
                                    // as we've seen in `into_raw()`)
                                    debug!("def_kind: {:?}", tcx.def_kind(defid));

                                    //debug!("dbg string: {:?}", tcx.def_path_debug_str(*defid));
                                    //if tcx.def_path_debug_str(*defid).contains("Animal::speak") {
                                    //    debug!("HARDCODED FIND");
                                    //    let first_ty = rawlist.type_at(0);
                                    //    debug!("***TYPE[0]: {:?}", first_ty);
                                    //    debug!("is_trait: {:?}", first_ty.is_trait());
                                    //    if first_ty.is_trait() {
                                    //        debug!("replace this!");
                                    //    }
                                    //}
                                }
                                _ => {}
                            }
                            //debug!("is_fn?: {:?}", ty.is_fn());
                            //debug!("is_impl_trait?: {:?}", ty.is_impl_trait());
                            //debug!("is_fn_ptr?: {:?}", ty.is_fn_ptr());
                            //debug!("is_trait?: {:?}", ty.is_trait());
                            //debug!("ptr_metadata_ty: {:?}", ty.ptr_metadata_ty(tcx, |ty| ty));
                            //debug!("pointee_metadata_ty_or_projection: {:?}", ty.pointee_metadata_ty_or_projection(tcx));
                        }
                    }
                }
            }
            debug!("args: {:?}", op_args);
            debug!("destination: {:?}", dst);
            debug!("target: {:?}", bb_opt);
            debug!("unwind: {:?}", unwind_act);
            debug!("call_source: {:?}", callsource);
            debug!("fn_span: {:?}", span);
            //for (i, arg) in op_args.into_iter().enumerate() {
            //    if i != 0 {
            //        continue;
            //    }
            //    match &arg.node {
            //        Operand::Move(place)
            //        | Operand::Copy(place) => {
            //            debug!("ArgOp: Move/Copy");
            //            let place_ty = place.ty(local_decls, tcx);
            //            let deref = place_ty.ty.builtin_deref(false);
            //            // FIXME this check also admits static dispatch
            //            // calls that simply happen to have a trait
            //            // object as their first argument
            //            // (e.g. Box::into_raw() takes in the trait
            //            // object we want to convert into a raw ptr)
            //            // TODO how else to differentiate?
            //            if deref.is_some() && deref.unwrap().is_trait() {
            //                debug!("-----REPLACE");
            //                debug!("deref: {:?}", deref.unwrap());
            //                //debug!("ptr_metadata_ty: {:?}", deref.unwrap().ptr_metadata_ty(tcx, |ty| ty));
            //                debug!("\n\n\n\n\n\n\n");
            //            }
            //        },
            //        Operand::Constant(_) => debug!("ArgOp: Const"),
            //    }
            //}
        }
        TerminatorKind::SwitchInt { discr: op, targets: switchtargets } => {
            debug!("SwitchInt");
            debug!("discr: {:?}", op);
            debug!("SwitchTargets-values: {:?}", switchtargets.all_values());
            debug!("SwitchTargets-targets: {:?}", switchtargets.all_targets());
        }
        TerminatorKind::Goto { target: bb } => {
            debug!("Goto");
            debug!("target: {:?}", bb);
        }
        TerminatorKind::Drop { place, target, unwind, replace, drop, async_fut } => {
            debug!("Drop");
            debug!("place: {:?}", place);
            debug!("target: {:?}", target);
            debug!("unwind: {:?}", unwind);
            debug!("replace: {:?}", replace);
            debug!("drop: {:?}", drop);
            debug!("async_fut: {:?}", async_fut);
        }
        _ => debug!("another"),
    }
}

