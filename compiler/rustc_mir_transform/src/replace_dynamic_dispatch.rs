//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent 
//! statically dispatched function calls. 

#![allow(dead_code)]
#![allow(unused_variables)]

use tracing::debug;

// FIXME precise imports
use rustc_middle::mir::*;
use rustc_middle::ty::*;
use rustc_span::*;
use rustc_span::source_map::Spanned;
use rustc_span::def_id::*;

use rustc_middle::ty::fast_reject::SimplifiedType;
use std::ops::Index;

use crate::patch::MirPatch;

pub(super) struct ReplaceDynamicDispatch;

struct SpeakBlockVars {
    bb_goto: BasicBlock,
    bb_cleanup: BasicBlock,
    raw_traitobj1_loc: Local,
    raw_traitobj2_loc: Local,
    empty_tup_loc: Local,
    concrete_ty_loc: Local,
    concrete_ty_did: DefId,
    speak_fn_did: DefId,
}

impl SpeakBlockVars {
    fn new(
        bb_goto: BasicBlock,
        bb_cleanup: BasicBlock,
        raw_traitobj1_loc: Local,
        raw_traitobj2_loc: Local,
        empty_tup_loc: Local,
        concrete_ty_loc: Local,
        concrete_ty_did: DefId,
        speak_fn_did: DefId,
    ) -> Self {
        SpeakBlockVars {
            bb_goto,
            bb_cleanup,
            raw_traitobj1_loc,
            raw_traitobj2_loc,
            empty_tup_loc,
            concrete_ty_loc,
            concrete_ty_did,
            speak_fn_did,
        }
    }
}

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() > 0 && !sess.emit_lifetime_markers()
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        debug!("LOCALS BEFORE ({:?})", body.local_decls().len());
        for (idx, local_decl) in body.local_decls().iter_enumerated() {
            debug!("-------idx: {:?}", idx);
            debug!("local_decl: {:?}", local_decl);
            debug!("mutability: {:?}", local_decl.mutability);
            debug!("ty: {:?}", local_decl.ty);
            id_ty(local_decl.ty);
        }

        let loc1 = Location { block: BasicBlock::from_u32(14), statement_index: 4 };
        let loc2 = Location { block: BasicBlock::from_u32(14), statement_index: 5 };
        let old_bb_len = body.basic_blocks.len();
        debug!("BBS LEN: {:?}", old_bb_len);
        if old_bb_len > 14 {
            debug!("STATEMENT BEFORE");
            debug!("stmt: {:?}", body.stmt_at(loc1));
        }

        debug!("RUN PASS");
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            debug!("BB: {:?}", bb);
            for stmt in data.statements.iter() {
                debug!("STMT: {:?}", stmt);
                id_stmt(&stmt.kind);
            }
            id_term(tcx, &data.terminator().kind);
            match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    if let Some((defid, rawlist)) = func.const_fn_def() {
                        if tcx.def_path_debug_str(defid).contains("Animal::speak") {
                            let to_defid: DefId;
                            let ty = rawlist.type_at(0);
                            id_ty(ty);
                            if ty.is_trait() {
                                debug!("ty: {:?}", ty);
                                replace_dynamic_dispatch(tcx, body, &mut patch, ty, bb, data, old_bb_len);
                            }
                        }
                    }
                }
                _ => {},
            }
        }

        patch.apply(body);

        let new_bb_len = body.basic_blocks.len();
        debug!("BBS LEN: {:?}", new_bb_len);
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if bb.as_usize() >= old_bb_len {
                debug!("NEW BB: {:?}", bb.as_usize());
                debug!("{:?}", data);
            }
        }

        if old_bb_len > 14 {
            debug!("STATEMENT AFTER");
            debug!("stmt: {:?}", body.stmt_at(loc1));
            //debug!("stmt: {:?}", body.stmt_at(loc2));
        }

        //debug!("LOCALS AFTER ({:?})", body.local_decls().len());
        //for (idx, local_decl) in body.local_decls().iter_enumerated() {
        //    debug!("-------idx: {:?}", idx);
        //    debug!("local_decl: {:?}", local_decl);
        //    debug!("mutability: {:?}", local_decl.mutability);
        //    debug!("ty: {:?}", local_decl.ty);
        //    //id_ty(local_decl.ty);
        //}
    }

    fn is_required(&self) -> bool {
        true
    }
}

fn replace_dynamic_dispatch<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    patch: &mut MirPatch<'tcx>,
    ty: Ty<'tcx>,
    bb: BasicBlock,
    data: &BasicBlockData<'tcx>,
    bb_len: usize,
) {
    debug!("-----REPLACE");

    let to_defid: DefId;
    match ty.kind() {
        Dynamic(rawlist, ..) => {
            if rawlist.len() > 0 {
                let principal_did_opt = (*rawlist).principal_def_id();
                if let Some(did) = principal_did_opt {
                    to_defid = did;
                } else {
                    debug!("auto traits only - nothing to replace");
                    return;
                }
            } else {
                return;
            }
        },
        // realistically can just return, but panicking for now to see
        // if this is ever triggered
        _ => panic!("trait is not Dynamic"),
    }

    // get trait impl defids
    // alternatively, replace trait_impls_of() => all_impls()
    let nb_impls_dids = tcx.trait_impls_of(to_defid).non_blanket_impls();
    debug!("non-blanket dids: {:?}", nb_impls_dids);
    let impls_keys = nb_impls_dids.keys();
    let mut impls_vals = nb_impls_dids.values();

    let cat_did;
    let cat_simp = impls_keys.index(1);
    match cat_simp {
        SimplifiedType::Adt(did) => cat_did = did,
        _ => panic!("impl is not Adt"),
    }

    let cat_did_for_assoc_items = impls_vals.nth(1).unwrap().as_slice()[0];
    debug!("cat_did_for_assoc_items: {:?}", cat_did_for_assoc_items);

    // dummy init value b/c the compiler thinks we can 
    // proceed with an uninit value despite the `init` flag
    let mut cat_speak_did = DefId { index: DefIndex::from_u32(0), krate: CrateNum::from_u32(0) };
    let mut init = false;
    for assoc_item in tcx.associated_items(cat_did_for_assoc_items).in_definition_order() {
        cat_speak_did = assoc_item.def_id;
        init = true;
    }
    if !init {
        panic!("no assoc items!");
    }

    // try: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.vtable_entries
    // - could potentially replace our get_cat() and get_dog() fakes

    // add locals
    let const_dyn_traitobj_loc = add_const_dyn_traitobj_temp(tcx, patch, ty);
    let dyn_metadata_loc = add_dynmetadata_temp(tcx, patch, to_defid);
    let raw_traitobj1_loc = add_raw_traitobj_temp(tcx, patch);
    let raw_traitobj2_loc = add_raw_traitobj_temp(tcx, patch);
    let empty_tup_loc = add_emptytup_temp(tcx, patch);
    let cat_loc = add_catref_temp(tcx, patch, *cat_did);
    let bool_loc = add_mut_bool_temp(tcx, patch);

    let hardcoded_bb_cleanup = BasicBlock::from_u32(21);

    // add blocks backwards to correctly connect edges...

    let bb_cat_goto = add_cat_goto_block(tcx, patch);
    let bb_cat_speak = add_cat_speak_block(tcx, patch, SpeakBlockVars::new(
        bb_cat_goto, 
        hardcoded_bb_cleanup, 
        raw_traitobj1_loc, 
        raw_traitobj2_loc, 
        empty_tup_loc, 
        cat_loc, 
        *cat_did, 
        cat_speak_did
    ));
    let bb_first_switch = add_first_switch_block(tcx, patch, bb_cat_speak, hardcoded_bb_cleanup, bool_loc);



    // /////////////////////////
    // add block (first switch):
    // - switchInt
    // /////////////////////////

    // /////////////////////////
    // add block (first compare):
    // - (PtrToPtr)
    // - ref
    // - ref
    // - Eq
    // /////////////////////////






    // /////////////////////////
    // replace current call with:
    // - &raw const
    // - ptr_metadata call
    //
    // [old bb] = [rw bb]
    // bb15 = bb28
    // bb21 = bb33 (cleanup)
    //
    // maintain target/unwind bb links
    // - old target: bb15 - drop dog (_20)
    // - new target: bb (len)? (how to ref non-brittle-y?)
    // /////////////////////////
    //add_raw_const(tcx, patch, bb, const_dyn_traitobj_loc);
    //add_ptrmetadata_call(tcx, body, patch, to_defid, bb, data, bb_len, const_dyn_traitobj_loc, dyn_metadata_loc);



    // /////////////////////////
    // add block (cat ptr_metadata):
    // - copy std::ptr::Unique<dyn Animal>.0: std::ptr::NonNull<dyn Animal>) as *const dyn Animal (Transmute);
    // - &*
    // - &raw const
    // - ptr_metadata call
    // /////////////////////////

    // /////////////////////////
    // add block (dog ptr_metadata) - same as above
    // /////////////////////////

    // /////////////////////////
    // add block (animal into_raw):
    // - const false (?)
    // - move
    // - into_raw
    // /////////////////////////



    // /////////////////////////
    // add block (second compare) - like first compare
    // /////////////////////////

    // /////////////////////////
    // add block (second switch) - like first switch
    // /////////////////////////

    // /////////////////////////
    // add block (dog speak) - like cat speak
    // /////////////////////////

    // /////////////////////////
    // add block (dog goto) ? - like cat goto
    // /////////////////////////



    // /////////////////////////
    // make sure cleanup funnels to the same place
    // /////////////////////////
}

fn dummy_span() -> Span {
    Span::new(BytePos(0), BytePos(0), SyntaxContext::root(), None)
}

fn dummy_source_info() -> SourceInfo {
    SourceInfo {
        span: dummy_span(),
        scope: SourceScope::ZERO,
    }
}

fn make_empty_tup<'tcx>(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    let tup_inner: &[Ty<'tcx>] = &[];
    Ty::new_tup(tcx, tup_inner)
}

fn add_const_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    ty: Ty<'tcx>,
) -> Local {
    // /////////////////////////
    // [og place] = [rw place] (n == new local)
    // _24 = _51
    // _22 = _23
    // _25n = _22 (*const dyn Animal)
    // _26n = _21 (DynMetadata<dyn Animal>)
    //
    // new local: 
    // - let mut _22: *const dyn Animal;
    // /////////////////////////

    // get dyn Animal
    let dyn_traitobj = ty.clone();

    // add *const dyn Animal local to patch
    patch.new_temp(
        Ty::new_imm_ptr(
            tcx,
            dyn_traitobj,
        ),
        dummy_span(),
    )
}

fn add_dynmetadata_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    to_defid: DefId,
) -> Local {
    // /////////////////////////
    // [og place] = [rw place] (n == new local)
    // _24 = _51
    // _22 = _23
    // _25n = _22 (*const dyn Animal)
    // _26n = _21 (DynMetadata<dyn Animal>)
    //
    // new local: 
    // - scope 5 { let _21: std::ptr::DynMetadata<dyn Animal>; ... }
    // /////////////////////////

    // get DynMetadata AdtDef
    let dynmetadata_adt_def = tcx.adt_def(tcx.lang_items().dyn_metadata().unwrap());

    // construct args list (containing dyn Animal)
    let dummy_args: Vec<GenericArg<'tcx>> = Vec::new();
    let pep_list = tcx.mk_poly_existential_predicates(&[Binder::dummy(ExistentialPredicate::Trait(
        ExistentialTraitRef::new(
            tcx,
            to_defid,
            dummy_args,
        )
    ))]);
    let trait_obj_tykind = Dynamic(
        pep_list,
        Region::new_from_kind(tcx, RegionKind::ReErased),
        DynKind::Dyn,
    );
    let trait_obj_ty = tcx.mk_ty_from_kind(trait_obj_tykind);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(trait_obj_ty)]);

    // add DynMetadata local to patch
    patch.new_temp(
        Ty::new_adt(
            tcx,
            dynmetadata_adt_def,
            gen_args_ref,
        ),
        dummy_span(),
    )
}

fn add_raw_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> Local {
    // /////////////////////////
    // new local: 
    // - scope 8 { let _30: *const (); ... }
    // /////////////////////////
    patch.new_temp(
        Ty::new_imm_ptr(
            tcx,
            make_empty_tup(tcx),
        ),
        dummy_span(),
    )
}

fn add_emptytup_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> Local {
    patch.new_temp(make_empty_tup(tcx), dummy_span())
}

fn add_catref_temp<'tcx>(
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
            Ty::new_adt(
                tcx,
                cat_adt_def,
                gen_args_ref,
            ),
            Mutability::Not,
        ),
        dummy_span(),
    )
}

fn add_mut_bool_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> Local {
    patch.new_temp(
        Ty::new(tcx, TyKind::Bool),
        dummy_span(),
    )
}

fn add_cat_goto_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> BasicBlock {
    // TODO construct statements (storage live/dead)

    // construct terminator
    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::Goto { target: BasicBlock::from_u32(15) },
    };

    let bb_data = BasicBlockData::new(Some(term), false);
    // if statements, use BBD::new_stmts()
    patch.new_block(bb_data)
}

fn add_cat_speak_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    sbv: SpeakBlockVars,
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

    // copy raw_animal ptr
    stmts.push(Statement::new(dummy_source_info(), StatementKind::Assign(
        Box::new((
            Place { local: sbv.raw_traitobj2_loc, projection: empty_proj },
            Rvalue::Use(Operand::Copy(Place { local: sbv.raw_traitobj1_loc, projection: empty_proj })),
        ))
    )));

    // transmute raw_animal copy into &Cat
    let cat_adt_def = tcx.adt_def(sbv.concrete_ty_did);
    let gen_args: &[GenericArg<'tcx>] = &[];
    let gen_args_ref = tcx.mk_args(gen_args);

    stmts.push(Statement::new(dummy_source_info(), StatementKind::Assign(
        Box::new((
            Place { local: sbv.concrete_ty_loc, projection: empty_proj },
            Rvalue::Cast(
                CastKind::Transmute,
                Operand::Move(Place { local: sbv.raw_traitobj2_loc, projection: empty_proj }),
                Ty::new_ref(
                    tcx,
                    Region::new_from_kind(tcx, RegionKind::ReErased),
                    Ty::new_adt(
                        tcx,
                        cat_adt_def,
                        gen_args_ref,
                    ),
                    Mutability::Not,
                ),
            ),
        ))
    )));

    // why &*s? try just using result of prev as speak arg

    // construct Cat::speak call
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let spanned_slice: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
        node: Operand::Move(Place { local: sbv.concrete_ty_loc, projection: empty_proj }),
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
                    Ty::new_fn_def(
                        tcx,
                        sbv.speak_fn_did, 
                        gen_args_ref,
                    ),
                ),
            })),
            args: spanned_slice,
            destination: Place { local: sbv.empty_tup_loc, projection: empty_proj },
            target: Some(sbv.bb_goto),
            unwind: UnwindAction::Cleanup(sbv.bb_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        },
    };

    let bb_data = BasicBlockData::new_stmts(stmts, Some(term), false);
    patch.new_block(bb_data)
}

fn add_first_switch_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb_speak: BasicBlock,
    bb_cleanup: BasicBlock,
    eq_res_loc: Local,
) -> BasicBlock {
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let targets = vec![(0u128, bb_speak)].into_iter();

    let term = Terminator {
        source_info: dummy_source_info(),
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Move(Place { local: eq_res_loc, projection: empty_proj }),
            targets: SwitchTargets::new(targets, bb_cleanup),
        },
    };

    let bb_data = BasicBlockData::new(Some(term), false);
    patch.new_block(bb_data)
}

fn add_raw_const<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
    bb: BasicBlock,
    const_dyn_traitobj_loc: Local,
) {
    let loc = Location { block: bb, statement_index: 4 };
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);
    patch.add_assign(
        loc,
        Place { local: const_dyn_traitobj_loc, projection: empty_proj },
        Rvalue::RawPtr(
            RawPtrKind::Const, 
            Place { local: Local::from_u32(22), projection: empty_proj },
        ),
    );
}

fn add_ptrmetadata_call<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    patch: &mut MirPatch<'tcx>,
    to_defid: DefId,
    bb: BasicBlock,
    data: &'a BasicBlockData<'tcx>,
    bb_len: usize,
    const_dyn_traitobj_loc: Local,
    dyn_metadata_loc: Local,
) -> TerminatorEdges<'a, 'tcx> {
    // get old terminator's edges
    let edges = data.terminator().kind.edges();
    //let old_return;
    let old_cleanup;
    match edges {
        TerminatorEdges::AssignOnReturn { return_, cleanup, .. } => {
            debug!("edges problems?");
            if return_.len() > 1 {
                debug!("RET: multiple return blocks");
            }
            if cleanup.is_none() {
                debug!("CLN: no cleanup");
            }
            //old_return = return_[0];
            old_cleanup = cleanup.unwrap();
        },
        _ => {
            debug!("another TerminatorEdges");
            panic!("verifopt: need to set terminator edges");
        }
    }

    // construct args list (containing dyn Animal)
    let dummy_args: Vec<GenericArg<'tcx>> = Vec::new();
    let pep_list = tcx.mk_poly_existential_predicates(&[Binder::dummy(ExistentialPredicate::Trait(
        ExistentialTraitRef::new(
            tcx,
            to_defid,
            dummy_args,
        )
    ))]);
    let trait_obj_tykind = Dynamic(
        pep_list,
        Region::new_from_kind(tcx, RegionKind::ReErased),
        DynKind::Dyn,
    );
    let trait_obj_ty = tcx.mk_ty_from_kind(trait_obj_tykind);
    let gen_args_ref = tcx.mk_args(&[GenericArg::from(trait_obj_ty)]);

    // make empty projection
    let empty_proj_slice: &[ProjectionElem<Local, Ty<'_>>] = &[];
    let empty_proj = tcx.mk_place_elems(empty_proj_slice);

    let spanned_slice: Box<[Spanned<Operand<'tcx>>]> = Box::new([Spanned {
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
            args: spanned_slice,
            destination: Place { local: dyn_metadata_loc, projection: empty_proj },
            target: Some(BasicBlock::from_usize(bb_len)),
            unwind: UnwindAction::Cleanup(old_cleanup),
            call_source: CallSource::Normal,
            fn_span: dummy_span(),
        }
    );

    // return old terminator's edges (patch has not been applied yet)
    edges
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
        },
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
        },
        crate::ty::Ref(reg, ty, m) => {
            debug!("Ref");
            debug!("region kind: {:?}", reg.kind());
            debug!("ty: {:?}", ty);
            id_ty(*ty);
            debug!("mut: {:?}", m);
        },
        crate::ty::FnDef(..) => debug!("FnDef"),
        crate::ty::FnPtr(..) => debug!("FnPtr"),
        crate::ty::UnsafeBinder(..) => debug!("UnsafeBinder"),
        crate::ty::Dynamic(rawlist, region, dynkind) => {
            debug!("Dynamic");
            debug!("region: {:?}", region.kind());
            debug!("dynkind: {:?}", dynkind);
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
                        },
                        _ => {}
                    }
                }
            }
        },
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
        },
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
                _ => {},
            }
        }
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
                },
                Rvalue::Cast(castkind, op, ty) => {
                    debug!("RValue Kind: Cast");
                    match castkind {
                        CastKind::PtrToPtr => debug!("CastKind: PtrToPtr"),
                        CastKind::Transmute => debug!("CastKind: Transmute"),
                        _ => debug!("CastKind: another"),
                    }
                    match op {
                        Operand::Copy(_) => debug!("Copy"),
                        Operand::Move(_) => debug!("Move"),
                        Operand::Constant(_) => debug!("Constant"),
                    }
                    debug!("Ty: {:?}", ty);
                    id_ty(ty);
                },
                Rvalue::RawPtr(rawptrkind, _place) => {
                    debug!("RValue Kind: RawPtr");
                    debug!("RawPtrKind::{:?}", rawptrkind);
                },
                _ => debug!("RValue Kind: another"),
            }
        }
        StatementKind::StorageLive(..) => debug!("StorageLive"),
        StatementKind::StorageDead(..) => debug!("StorageDead"),
        _ => debug!("another"),
    }
}

fn id_term<'tcx>(
    tcx: TyCtxt<'tcx>,
    kind: &TerminatorKind<'tcx>,
) {
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
                        },
                        rustc_middle::mir::Const::Unevaluated(uneval_const, ty) => {
                            debug!("Const::Unevaluated");
                            debug!("UnevaluatedConst: {:?}", uneval_const);
                            debug!("Ty: {:?}", ty);
                        },
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
                        },
                    }
                },
            }
            debug!("args: {:?}", op_args);
            debug!("destination: {:?}", dst);
            debug!("target: {:?}", bb_opt);
            debug!("unwind: {:?}", unwind_act);
            debug!("call_source: {:?}", callsource);
            debug!("fn_span: {:?}", span);
            /*
            for (i, arg) in op_args.into_iter().enumerate() {
                if i != 0 {
                    continue;
                }
                match &arg.node {
                    Operand::Move(place) 
                    | Operand::Copy(place) => {
                        debug!("ArgOp: Move/Copy");
                        let place_ty = place.ty(local_decls, tcx);
                        let deref = place_ty.ty.builtin_deref(false);
                        // FIXME this check also admits static dispatch 
                        // calls that simply happen to have a trait 
                        // object as their first argument 
                        // (e.g. Box::into_raw() takes in the trait 
                        // object we want to convert into a raw ptr)
                        // TODO how else to differentiate?
                        if deref.is_some() && deref.unwrap().is_trait() {
                            debug!("-----REPLACE");
                            debug!("deref: {:?}", deref.unwrap());
                            //debug!("ptr_metadata_ty: {:?}", deref.unwrap().ptr_metadata_ty(tcx, |ty| ty));
                            debug!("\n\n\n\n\n\n\n");
                        }
                    },
                    Operand::Constant(_) => debug!("ArgOp: Const"),
                }
            }
            */
        },
        TerminatorKind::SwitchInt {
            discr: op,
            targets: switchtargets, 
        } => {
            debug!("SwitchInt");
            debug!("discr: {:?}", op);
            debug!("SwitchTargets-values: {:?}", switchtargets.all_values());
            debug!("SwitchTargets-targets: {:?}", switchtargets.all_targets());
        },
        TerminatorKind::Goto { target: bb } => {
            debug!("Goto");
            debug!("target: {:?}", bb);
        },
        TerminatorKind::Drop {
            place, target, unwind, replace, drop, async_fut
        } => {
            debug!("Drop");
            debug!("place: {:?}", place);
            debug!("target: {:?}", target);
            debug!("unwind: {:?}", unwind);
            debug!("replace: {:?}", replace);
            debug!("drop: {:?}", drop);
            debug!("async_fut: {:?}", async_fut);
        },
        _ => debug!("another"),
    }
}

