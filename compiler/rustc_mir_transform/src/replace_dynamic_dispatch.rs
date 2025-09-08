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
        debug!("ReplaceDynamicDispatch");
        debug!("MIR Phase: {:?}", body.phase);
        debug!("body source: {:?}", body.source);

        // FIXME is there a better way to do this?? (sans clone)
        let binding = body.clone();
        let local_decls = binding.local_decls();

        for block in body.basic_blocks_mut() {
            debug!("\nNEW BLOCK\n\n\n");
            for statement in &block.statements {
                debug!("\nSTMT\n");
                match &statement.kind {
                    StatementKind::Assign(boxed_assign) => {
                        debug!("Statement Kind: Assign");
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
                            _ => debug!("RValue Kind: another"),
                        }
                    }
                    StatementKind::StorageLive(..) => debug!("Kind: StorageLive"),
                    StatementKind::StorageDead(..) => debug!("Kind: StorageDead"),
                    _ => debug!("Kind: another"),
                }
                debug!("{:?}", statement);
            }

            debug!("\nTERMINATORS\n");
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
                    debug!("TerminatorKind: Call");
                    debug!("Operand: {:?}", operand);
                    debug!("Args: {:?}", op_args);
                    debug!("Destination: {:?}", dst);
                    debug!("Target: {:?}", bb_opt);
                    debug!("Unwind: {:?}", unwind_act);
                    debug!("CallSource: {:?}", callsource);
                    debug!("FnSpan: {:?}", span);
                    for (i, arg) in op_args.into_iter().enumerate() {
                        if i != 0 {
                            continue;
                        }
                        match &arg.node {
                            Operand::Move(place) 
                            | Operand::Copy(place) => {
                                debug!("ArgOp: Move/Copy");
                                let place_ty = place.ty(local_decls, tcx);
                                //debug!("arg type: {:?}", place_ty);
                                let deref = place_ty.ty.builtin_deref(false);
                                if deref.is_some() && deref.unwrap().is_trait() {
                                    debug!("-----REPLACE\n\n\n\n\n\n\n");
                                }
                            },
                            Operand::Constant(_) => debug!("ArgOp: Const"),
                        }
                    }
                },
                TerminatorKind::SwitchInt {
                    discr: op,
                    targets: switchtargets, 
                } => {
                    debug!("TerminatorKind: SwitchInt");
                    debug!("Discr: {:?}", op);
                    debug!("SwitchTargets-values: {:?}", switchtargets.all_values());
                    debug!("SwitchTargets-targets: {:?}", switchtargets.all_targets());
                },
                _ => debug!("TerminatorKind: another"),
                //TerminatorKind::TailCall { .. } => debug!("TerminatorKind: TailCall"),
                //TerminatorKind::Goto { .. } => debug!("TerminatorKind: Goto"),
                //TerminatorKind::UnwindResume => debug!("TerminatorKind: UnwindResume"),
                //TerminatorKind::UnwindTerminate(_) => debug!("TerminatorKind: UnwindTerminate"),
                //TerminatorKind::Return => debug!("TerminatorKind: Return"),
                //TerminatorKind::Unreachable => debug!("TerminatorKind: Unreachable"),
                //TerminatorKind::Drop { .. } => debug!("TerminatorKind: Drop"),
                //TerminatorKind::Assert { .. } => debug!("TerminatorKind: Assert"),
                //TerminatorKind::Yield { .. } => debug!("TerminatorKind: Yield"),
                //TerminatorKind::CoroutineDrop => debug!("TerminatorKind: CoroutineDrop"),
                //TerminatorKind::FalseEdge { .. } => debug!("TerminatorKind: FalseEdge"),
                //TerminatorKind::FalseUnwind { .. } => debug!("TerminatorKind: FalseUnwind"),
                //TerminatorKind::InlineAsm { .. } => debug!("TerminatorKind: InlineAsm"),
            }
        }
    }

    fn is_required(&self) -> bool {
        true
    }
}
