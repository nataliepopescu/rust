//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent 
//! statically dispatched function calls. 

#![allow(dead_code)]
#![allow(unused_variables)]

use tracing::debug;

use rustc_middle::mir::*;
use rustc_middle::ty::*;
use rustc_span::*;
use rustc_span::def_id::*;

use crate::patch::MirPatch;

pub(super) struct ReplaceDynamicDispatch;

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() > 0 && !sess.emit_lifetime_markers()
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let mut patch = MirPatch::new(body);

        // FIXME is there a better way to do this?? (sans clone)
        //let binding = body.clone();
        //let local_decls = binding.local_decls();
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
            match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    if let Some((defid, rawlist)) = func.const_fn_def() {
                        if tcx.def_path_debug_str(defid).contains("Animal::speak") {
                            if rawlist.type_at(0).is_trait() {
                                replace_dynamic_dispatch(tcx, body, &mut patch, bb);
                            }
                        }
                    }
                }
                _ => {},
            }
        }

        patch.apply(body);

        debug!("LOCALS AFTER ({:?})", body.local_decls().len());
        for (idx, local_decl) in body.local_decls().iter_enumerated() {
            debug!("-------idx: {:?}", idx);
            debug!("local_decl: {:?}", local_decl);
            debug!("mutability: {:?}", local_decl.mutability);
            debug!("ty: {:?}", local_decl.ty);
            id_ty(local_decl.ty);
        }

    }

    fn is_required(&self) -> bool {
        true
    }
}

fn replace_dynamic_dispatch<'tcx>(
    tcx: TyCtxt<'tcx>,
    _body: &Body<'tcx>,
    patch: &mut MirPatch<'tcx>,
    _bb: BasicBlock,
) {
    debug!("-----REPLACE");

    // /////////////////////////
    // replace current call with:
    // - &raw const
    // - ptr_metadata call
    //
    // [og place] = [rw place]
    // _24 = _51
    // _22 = _23
    //
    // new locals: _22 and _21
    // - let mut _22: *const dyn Animal;
    // - scope 5 { let _21: std::ptr::DynMetadata<dyn Animal>; ... }
    //
    // maintain target/unwind bb links
    // - old target: bb14 - drop dog (_20)
    // - new target: bb28 (how to ref non-brittle-y?)
    // - old unwind: bb22 - cleanup drop dog (_20)
    // - new unwind: bb33 (how to ref non-brittle-y?)
    // /////////////////////////
    let _ = add_const_dyn_traitobj_temp(tcx, patch);
    let _ = add_dynmetadata_temp(tcx, patch);
    //add_raw_const();
    //add_pm_call();

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
    // add block (first compare):
    // - (PtrToPtr)
    // - ref
    // - ref
    // - Eq
    // /////////////////////////

    // /////////////////////////
    // add block (first switch):
    // - switchInt
    // /////////////////////////

    // /////////////////////////
    // add block (cat speak):
    // - copy
    // - Transmute
    // - &*
    // - &*
    // - speak
    // /////////////////////////

    // /////////////////////////
    // add block (cat goto) ?
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

fn add_const_dyn_traitobj_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> Local {
    // get list containing dyn Animal
    let dummy_args: Vec<GenericArg<'tcx>> = Vec::new();
    let pep_list = tcx.mk_poly_existential_predicates(&[Binder::dummy(ExistentialPredicate::Trait(
        ExistentialTraitRef::new(
            tcx,
            // TODO how to get this for arbitrary traits
            DefId { index: DefIndex::from_u32(3), krate: CrateNum::new(0) },
            dummy_args,
        )
    ))]);

    // get Dynamic
    let dyn_traitobj = Ty::new_dynamic(
        tcx,
        pep_list,
        Region::new_from_kind(tcx, ReErased),
        DynKind::Dyn,
    );

    // add *const dyn Animal local to patch
    patch.new_temp(
        // ty
        Ty::new_imm_ptr(
            tcx,
            dyn_traitobj,
        ),
        // dummy span
        Span::new(BytePos(0), BytePos(0), SyntaxContext::root(), None),
    )
}

fn add_dynmetadata_temp<'tcx>(
    tcx: TyCtxt<'tcx>,
    patch: &mut MirPatch<'tcx>,
) -> Local {
    // get DynMetadata AdtDef
    let dynmetadata_adt_def = tcx.adt_def(tcx.lang_items().dyn_metadata().unwrap());

    // construct DynMetadata GenericArgsRef
    let dummy_args: Vec<GenericArg<'tcx>> = Vec::new();
    let pep_list = tcx.mk_poly_existential_predicates(&[Binder::dummy(ExistentialPredicate::Trait(
        ExistentialTraitRef::new(
            tcx,
            // TODO how to get this for arbitrary traits
            DefId { index: DefIndex::from_u32(3), krate: CrateNum::new(0) },
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
        // ty
        Ty::new_adt(
            tcx,
            dynmetadata_adt_def,
            gen_args_ref,
        ),
        // dummy span
        Span::new(BytePos(0), BytePos(0), SyntaxContext::root(), None),
    )
}

// Identification helpers

fn id_ty<'tcx>(ty: Ty<'tcx>) {
    debug!("-TyKind:");
    match ty.kind() {
        crate::ty::Bool => debug!("Bool"),
        crate::ty::RawPtr(ty, m) => {
            debug!("RawPtr");
            debug!("mut: {:?}", m);
            debug!("inner ty: {:?}", ty);
            id_ty(*ty);
        },
        crate::ty::Ref(reg, ty, m) => {
            debug!("Ref");
            debug!("reg: {:?}", reg);
            debug!("ty: {:?}", ty);
            debug!("mut: {:?}", m);
        },
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
        crate::ty::FnDef(..) => debug!("FnDef"),
        crate::ty::FnPtr(..) => debug!("FnPtr"),
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
        crate::ty::Pat(..) => debug!("Pat"),
        _ => debug!("another"),
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

/*
for block in body.basic_blocks_mut() {
    debug!("\n\n\n\nNEW BLOCK\n");
    for statement in &block.statements {
        debug!("--StatementKind:");
        match &statement.kind {
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
                            BorrowKind::Shared => debug!("BorrowKind: Shared"),
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
        debug!("{:?}", statement);
    }

    debug!("--TerminatorKind:");
    // try to ID what to rewrite
    match &block.terminator().kind {
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
                        Const::Ty(ty, c) => {
                            debug!("Const::Ty");
                            debug!("ty: {:?}", ty);
                            debug!("const: {:?}", c);
                        },
                        Const::Unevaluated(uneval_const, ty) => {
                            debug!("Const::Unevaluated");
                            debug!("UnevaluatedConst: {:?}", uneval_const);
                            debug!("Ty: {:?}", ty);
                        },
                        Const::Val(const_val, ty) => {
                            debug!("Const::Val");
                            debug!("ConstValue: {:?}", const_val);
                            debug!("Ty: {:?}", ty);
                            match ty.kind() {
                                crate::ty::FnDef(defid, rawlist) => {
                                    debug!("defid: {:?}", defid);
                                    debug!("rawlist: {:?}", rawlist);
                                    // TODO check expected type of 
                                    // first parameter here (_not_ the 
                                    // arg, which may happen to be dyn,
                                    // as we've seen in `into_raw()`)
                                    debug!("def_kind: {:?}", tcx.def_kind(defid));
                                    debug!("dbg string: {:?}", tcx.def_path_debug_str(*defid));
                                    if tcx.def_path_debug_str(*defid).contains("Animal::speak") {
                                        debug!("HARDCODED FIND");
                                        let first_ty = rawlist.type_at(0);
                                        debug!("***TYPE[0]: {:?}", first_ty);
                                        debug!("is_trait: {:?}", first_ty.is_trait());
                                        if first_ty.is_trait() {
                                            debug!("-----REPLACE");
                                        }
                                    }
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
*/
