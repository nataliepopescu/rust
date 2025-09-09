//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent 
//! statically dispatched function calls. 

use tracing::debug;

use rustc_middle::mir::*;
use rustc_middle::ty::{RegionKind, TyCtxt};

pub(super) struct ReplaceDynamicDispatch;

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() > 0 && !sess.emit_lifetime_markers()
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        //debug!("ReplaceDynamicDispatch");
        //debug!("MIR Phase: {:?}", body.phase);
        //debug!("body source: {:?}", body.source);

        // FIXME is there a better way to do this?? (sans clone)
        //let binding = body.clone();
        //let local_decls = binding.local_decls();

        /*
        for block in body.basic_blocks_mut() {
            match &block.terminator().kind {
                TerminatorKind::Call {
                    func, 
                    args, 
                    destination,
                    target,
                    unwind, 
                    ..,
                } => {

                }
                _ => {},
            }
        }
        */

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
    }

    fn is_required(&self) -> bool {
        true
    }
}
