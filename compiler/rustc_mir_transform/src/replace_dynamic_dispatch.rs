//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent
//! statically dispatched function calls.

//#![allow(dead_code)]
#![allow(unused_variables)]

//#![allow(rustc::default_hash_types)]
//use std::collections::HashSet;

// FIXME precise imports

//use rustc_middle::mir::{Statement, Terminator, StatementKind, TerminatorKind, Operand, CastKind, Rvalue, BinOp, PlaceElem, PlaceRef, Place, UnwindAction, CallSource, ConstOperand, ConstValue, Local, ProjectionElem, BasicBlock, BasicBlockData, RawPtrKind, Location, SwitchTargets, SourceInfo, SourceScope, Body, TerminatorEdges};
use rustc_index::IndexSlice;
use rustc_middle::mir::*;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::*;
use rustc_span::def_id::*;
use rustc_span::source_map::Spanned;
use rustc_span::*;

//use tracing::debug;

use crate::patch::MirPatch;

use crate::verifopt_analysis::FlowInterp;

pub(super) struct ReplaceDynamicDispatch;

const DUMMY_DEFID: DefId = DefId { index: DefIndex::from_u32(0), krate: CrateNum::from_u32(0) };
// FIXME change from magic num -> dynamic
const INTO_RAW_FN_DEFID: DefId = DefId { index: DefIndex::from_u32(731), krate: CrateNum::from_u32(3) };
const EQ_FN_DEFID: DefId = DefId { index: DefIndex::from_u32(3216), krate: CrateNum::from_u32(2) };

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {

        /* FLOW ANALYSIS */

        let mut flow_interp = FlowInterp::new();
        flow_interp.visit_body(body);

        /* TRANSFORMATION */

        let mut patch = MirPatch::new(body);
        let old_locals = body.local_decls();

        //debug!("--START GET DEFIDS--");
        //debug!("{:?}", tcx.all_diagnostic_items(()));
        //debug!("--END GET DEFIDS--");

        //debug!("RUN PASS");
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            //debug!("BB: {:?}", bb);
            //for stmt in &data.statements{
            //    id_stmt(&stmt.kind);
            //}
            //id_term(tcx, &data.terminator().kind);
            match &data.terminator().kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if let Some((defid, rawlist)) = func.const_fn_def() {
                        if tcx.def_path_debug_str(defid).contains("Animal::kaeps") {
                            let ty = rawlist.type_at(0);
                            //id_ty(ty);
                            if ty.is_trait() {
                                //debug!("ty: {:?}", ty);
                                let num_bbs = body.basic_blocks.len();
                                replace_dynamic_dispatch_bmarks(tcx, &mut patch, old_locals, ty, *destination, bb, data, num_bbs);
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
    let mut fn_did = DUMMY_DEFID;
    for assoc_item in tcx.associated_items(assoc_items_did).in_definition_order() {
        //debug!("assoc_item: {:?}", assoc_item);
        //debug!("assoc_item.def_id: {:?}", assoc_item.def_id);
        fn_did = assoc_item.def_id;
        init = true;
    }
    if !init {
        panic!("no assoc items!");
    }

    (*ty_did, fn_did)
}

fn get_bbs<'tcx>(
    data: &BasicBlockData<'tcx>,
) -> (BasicBlock, BasicBlock) {
    let edges = data.terminator().kind.edges();
    let bb_old_next;
    let bb_old_cleanup;
    match edges {
        TerminatorEdges::AssignOnReturn { return_, cleanup, .. } => {
            //debug!("edges problems?");
            if return_.len() > 1 {
                panic!("RET: multiple return blocks");
            }
            if cleanup.is_none() {
                panic!("CLN: no cleanup");
            }
            bb_old_next = return_[0];
            bb_old_cleanup = cleanup.unwrap();
        }
        _ => {
            panic!("verifopt: need to set terminator edges");
        }
    }
    (bb_old_next, bb_old_cleanup)
}

fn get_traitobj_did<'tcx>(
    ty: Ty<'tcx>,
) -> DefId {
    let traitobj_did: Option<DefId>;
    match ty.kind() {
        Dynamic(rawlist, ..) => {
            if rawlist.len() > 0 {
                let principal_did_opt = (*rawlist).principal_def_id();
                if let Some(did) = principal_did_opt {
                    traitobj_did = Some(did);
                } else {
                    panic!("auto traits only - nothing to replace");
                }
            } else {
                traitobj_did = None;
            }
        }
        // realistically can just return, but panicking for now to see
        // if this is ever triggered
        _ => panic!("trait is not Dynamic"),
    }
    if traitobj_did.is_none() {
        panic!("no traitobj_did found");
    }
    traitobj_did.unwrap()
}

fn dyndispatch_retval<'tcx>(
    old_locals: &IndexSlice<Local, LocalDecl<'tcx>>,
    term_dst_place: Place<'tcx>,
) -> bool {
    if old_locals.get(term_dst_place.local).is_some() {
        true
    } else {
        false
    }
}

fn replace_dynamic_dispatch_bmarks<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    old_locals: &IndexSlice<Local, LocalDecl<'tcx>>,
    ty: Ty<'tcx>,
    term_dst_place: Place<'tcx>,
    bb: BasicBlock,
    data: &BasicBlockData<'tcx>,
    num_bbs: usize,
) {
    // get old terminator's edges
    let (bb_old_next, bb_old_cleanup) = get_bbs(data);
    let has_retval = dyndispatch_retval(old_locals, term_dst_place);
    let bb_old_return;
    if has_retval {
        bb_old_return = bb_old_next + 1;
    } else {
        bb_old_return = bb_old_next;
    }

    let bb_into_raw_exp = BasicBlock::from_usize(num_bbs);

    let traitobj_did = get_traitobj_did(ty);

    let impls = tcx.trait_impls_of(traitobj_did);
    let nb_impls_dids = impls.non_blanket_impls();
    let impls_keys: Vec<_> = nb_impls_dids.keys().collect();
    let impls_vals: Vec<_> = nb_impls_dids.values().collect();
    let (cat_did, cat_speak_did) =
        get_dids(tcx, impls_keys.get(0).unwrap(), impls_vals.get(0).unwrap().as_slice()[0]);
    let (dog_did, dog_speak_did) =
        get_dids(tcx, impls_keys.get(1).unwrap(), impls_vals.get(1).unwrap().as_slice()[0]);

    assert_eq!(bb_old_next.as_usize(), 1);
    assert_eq!(bb_old_cleanup.as_usize(), 3);
    assert_eq!(bb_into_raw_exp.as_usize(), 5);

    let retval = Local::from_u32(0);
    let animal = Local::from_u32(1);
    let animal_vtable = Local::from_u32(2);
    let cat_vtable = Local::from_u32(3);

    // mod cur speak block w/ goto new start (into_raw)
    replace_dyndispatch_term_w_goto(patch, bb, bb_into_raw_exp);

    // into_raw
    let mut_dyn_traitobj = add_mut_dyn_traitobj_temp(tcx, patch, traitobj_did);
    let boxed_dyn_traitobj1 = add_boxed_dyn_traitobj_temp(tcx, patch, traitobj_did);

    let bb_first_compare_exp = BasicBlock::from_usize(bb_into_raw_exp.as_usize() + 1);
    let bb_into_raw_act = add_into_raw_block(
        tcx,
        patch,
        bb_first_compare_exp,
        bb_old_cleanup,
        mut_dyn_traitobj,
        boxed_dyn_traitobj1,
        animal,
        traitobj_did,
        None,
    );
    assert_eq!(bb_into_raw_act, bb_into_raw_exp);

    // TODO for loop -> compare/switch blocks (n-1)

    // TODO for loop -> speak/goto blocks (n)

    // first_comparison
    let raw_traitobj1 = add_raw_traitobj_temp(tcx, patch);
    let animal_vtable_ref = add_dynmetadata_ref_temp(tcx, patch, traitobj_did);
    let cat_vtable_ref = add_dynmetadata_ref_temp(tcx, patch, traitobj_did);
    let first_eq_res = add_mut_bool_temp(tcx, patch);

    let bb_first_switch_exp = BasicBlock::from_usize(bb_first_compare_exp.as_usize() + 1);
    let bb_first_compare_act = add_compare_vtable_block(
        tcx,
        patch,
        bb_first_switch_exp,
        bb_old_cleanup,
        raw_traitobj1,
        mut_dyn_traitobj,
        animal_vtable,
        animal_vtable_ref,
        cat_vtable,
        cat_vtable_ref,
        first_eq_res,
        traitobj_did,
        false,
        Some(vec![boxed_dyn_traitobj1]),
    );
    assert_eq!(bb_first_compare_act, bb_first_compare_exp);

    // first_switch
    let bb_cat_speak_exp = BasicBlock::from_usize(bb_first_switch_exp.as_usize() + 1);
    let bb_dog_speak_exp = BasicBlock::from_usize(bb_cat_speak_exp.as_usize() + 2);
    let bb_first_switch_act =
        add_switch_block(tcx, patch, bb_cat_speak_exp, bb_dog_speak_exp, first_eq_res);
    assert_eq!(bb_first_switch_exp, bb_first_switch_act);

    // first_speak
    let raw_traitobj2 = add_raw_traitobj_temp(tcx, patch);
    let cat_obj = add_concretety_ref_temp(tcx, patch, cat_did);

    let bb_cat_ret_exp = BasicBlock::from_usize(bb_cat_speak_exp.as_usize() + 1);
    let bb_cat_speak_act = add_speak_block(
        tcx,
        patch,
        bb_cat_ret_exp,
        bb_old_cleanup,
        raw_traitobj1,
        raw_traitobj2,
        retval,
        cat_obj,
        cat_did,
        cat_speak_did,
        None,
    );
    assert_eq!(bb_cat_speak_exp, bb_cat_speak_act);

    // goto (to bb_old_return)
    let bb_cat_ret_act = add_goto_block(patch, bb_old_return);
    assert_eq!(bb_cat_ret_exp, bb_cat_ret_act);

    // second_speak
    let raw_traitobj4 = add_raw_traitobj_temp(tcx, patch);
    let dog_obj = add_concretety_ref_temp(tcx, patch, dog_did);

    let bb_dog_ret_exp = BasicBlock::from_usize(bb_dog_speak_exp.as_usize() + 1);
    let bb_dog_speak_act = add_speak_block(
        tcx,
        patch,
        bb_dog_ret_exp,
        bb_old_cleanup,
        raw_traitobj1,
        raw_traitobj4,
        retval,
        dog_obj,
        dog_did,
        dog_speak_did,
        None,
    );
    assert_eq!(bb_dog_speak_exp, bb_dog_speak_act);

    // goto (to bb_old_return)
    let bb_dog_ret_act = add_goto_block(patch, bb_old_return);
    assert_eq!(bb_dog_ret_exp, bb_dog_ret_act);
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
//fn add_emptytup_temp<'tcx>(tcx: TyCtxt<'tcx>, patch: &mut MirPatch<'tcx>) -> Local {
//    patch.new_temp(make_empty_tup(tcx), dummy_span())
//}

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
    bb_ret: BasicBlock,
) -> BasicBlock {
    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Goto { target: bb_ret },
    };

    let bb_data = BasicBlockData::new(Some(term), false);
    patch.new_block(bb_data)
}

fn add_speak_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_ret: BasicBlock,
    bb_cleanup: BasicBlock,
    raw_traitobj1_loc: Local,
    raw_traitobj2_loc: Local,
    func_ret_loc: Local,
    concrete_ty_loc: Local,
    concrete_ty_did: DefId,
    speak_fn_did: DefId,
    to_free_opt: Option<Vec<Local>>,
    //set: &mut HashSet<Local>,
) -> BasicBlock {
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);
    let mut stmts = Vec::new();

    if let Some(to_free_vec) = to_free_opt {
        for to_free in to_free_vec.iter() {
            stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(*to_free)));
        }
    }

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(raw_traitobj2_loc)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(concrete_ty_loc)));
    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(func_ret_loc)));

    // copy raw_animal ptr
    //debug!("SET INSERT RES: {} - 0", set.insert(raw_traitobj2_loc));
    //debug!("loc: {:?}", raw_traitobj2_loc);
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

    //debug!("SET INSERT RES: {} - 1", set.insert(concrete_ty_loc));
    //debug!("loc: {:?}", concrete_ty_loc);
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

    //debug!("SET INSERT RES: {} - 2", set.insert(func_ret_loc));
    //debug!("loc: {:?}", func_ret_loc);
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
            target: Some(bb_ret),
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
    to_free_opt: Option<Vec<Local>>,
    //set: &mut HashSet<Local>,
) -> BasicBlock {
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();

    if let Some(to_free_vec) = to_free_opt {
        for to_free in to_free_vec.iter() {
            stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(*to_free)));
        }
    }

    stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageLive(raw_traitobj1_loc)));

    if !done_copy {
        //debug!("SET INSERT RES: {} - 3", set.insert(raw_traitobj1_loc));
        //debug!("loc: {:?}", raw_traitobj1_loc);
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
    }

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

    //debug!("DM TO REF LOCAL: {:?}", dynmetadata_traitobj_ref_loc);
    //debug!("DM TO LOCAL: {:?}", dynmetadata_traitobj_loc);
    //debug!("SET INSERT RES: {} - 4", set.insert(dynmetadata_traitobj_ref_loc));
    //debug!("loc: {:?}", dynmetadata_traitobj_ref_loc);
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

    //debug!("DM CT REF LOCAL: {:?}", dynmetadata_concretety_ref_loc);
    //debug!("DM CT LOCAL: {:?}", dynmetadata_concretety_loc);
    //debug!("SET INSERT RES: {} - 5", set.insert(dynmetadata_concretety_ref_loc));
    //debug!("loc: {:?}", dynmetadata_concretety_ref_loc);
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

    //debug!("SET INSERT RES: {} - 6", set.insert(eq_res_loc));
    //debug!("loc: {:?}", eq_res_loc);
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
                        EQ_FN_DEFID,
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
    to_free_opt: Option<Vec<Local>>,
    //set: &mut HashSet<Local>,
) -> BasicBlock {
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let mut stmts: Vec<Statement<'tcx>> = Vec::new();

    if let Some(to_free_vec) = to_free_opt {
        for to_free in to_free_vec.iter() {
            stmts.push(Statement::new(dummy_source_info(), StatementKind::StorageDead(*to_free)));
        }
    }

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

    //debug!("SET INSERT RES: {} - 7", set.insert(boxed_dyn_traitobj_loc));
    //debug!("loc: {:?}", boxed_dyn_traitobj_loc);
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
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(dyn_traitobj_ty)]);

    let args: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: boxed_dyn_traitobj_loc, projection: empty_proj }),
        span: dummy_span(),
    }]);

    //debug!("SET INSERT RES: {} - 8", set.insert(mut_dyn_traitobj_loc));
    //debug!("loc: {:?}", mut_dyn_traitobj_loc);
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
                        INTO_RAW_FN_DEFID,
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

fn replace_dyndispatch_term_w_goto<'tcx>(
    patch: &mut MirPatch<'tcx>,
    cur_bb: BasicBlock,
    new_start: BasicBlock,
) {
    // replace term w goto
    patch.patch_terminator(
        cur_bb,
        TerminatorKind::Goto { target: new_start },
    );
}

// Identification helpers

/*
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
                                    for (gidx, genarg) in rawlist.iter().enumerate() {
                                        debug!("--GENARGSidx: {:?}", gidx);
                                        let type_opt = genarg.as_type();
                                        debug!("kind: {:?}", genarg.kind());
                                        match genarg.kind() {
                                            GenericArgKind::Type(inner_ty) => {
                                                debug!("inner_ty: {:?}", inner_ty);
                                                debug!("inner_ty.kind(): {:?}", inner_ty.kind());
                                            },
                                            _ => debug!("another"),
                                        }
                                        debug!("as_region: {:?}", genarg.as_region());
                                        debug!("as_type: {:?}", type_opt);
                                        debug!("as_const: {:?}", genarg.as_const());
                                        if type_opt.is_some() {
                                            id_ty(type_opt.unwrap());
                                        }
                                    }
                                    // TODO check expected type of
                                    // first parameter here (_not_ the
                                    // arg, which may happen to be dyn,
                                    // as we've seen in `into_raw()`)
                                    debug!("def_kind: {:?}", tcx.def_kind(defid));

                                    //debug!("dbg string: {:?}", tcx.def_path_debug_str(*defid));
                                    //if tcx.def_path_debug_str(*defid).contains("Animal::kaeps") {
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
*/

