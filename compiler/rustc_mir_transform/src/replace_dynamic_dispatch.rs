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

        debug!("\nBEGINNING\n");
        for block in body.basic_blocks_mut() {
            debug!("\nNEW BLOCK\n");
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
                                    //RegionKind::ReEarlyParam(..) => debug!("RegionKind: ReEarlyParam"),
                                    //RegionKind::ReBound(..) => debug!("RegionKind: ReBound"),
                                    //RegionKind::ReLateParam(..) => debug!("RegionKind: ReLateParam"),
                                    //RegionKind::ReStatic => debug!("RegionKind: ReStatic"),
                                    //RegionKind::ReVar(..) => debug!("RegionKind: ReVar"),
                                    //RegionKind::RePlaceholder(..) => debug!("RegionKind: RePlaceHolder"),
                                    //RegionKind::ReError(..) => debug!("RegionKind: ReError"),
                                }
                                match borrowkind {
                                    BorrowKind::Shared => debug!("BorrowKind: Shared"),
                                    _ => debug!("BorrowKind: another"),
                                    //BorrowKind::Fake(_) => debug!("BorrowKind: Fake"),
                                    //BorrowKind::Mut { kind: _ } => debug!("BorrowKind: Mut"),
                                }
                            },
                            _ => debug!("RValue Kind: another"),
                            //Rvalue::Repeat(..) => debug!("RValue Kind: Repeat"),
                            //Rvalue::ThreadLocalRef(..) => debug!("RValue Kind: ThreadLocalRef"),
                            //Rvalue::RawPtr(..) => debug!("RValue Kind: RawPtr"),
                            //Rvalue::Len(..) => debug!("RValue Kind: Len"),
                            //Rvalue::Cast(..) => debug!("RValue Kind: Cast"),
                            //Rvalue::NullaryOp(..) => debug!("RValue Kind: NullaryOp"),
                            //Rvalue::UnaryOp(..) => debug!("RValue Kind: UnaryOp"),
                            //Rvalue::Discriminant(..) => debug!("RValue Kind: Discriminant"),
                            //Rvalue::Aggregate(..) => debug!("RValue Kind: Aggregate"),
                            //Rvalue::ShallowInitBox(..) => debug!("RValue Kind: ShallowInitBox"),
                            //Rvalue::CopyForDeref(..) => debug!("RValue Kind: CopyForDeref"),
                            //Rvalue::WrapUnsafeBinder(..) => debug!("RValue Kind: WrapUnsafeBinder"),
                        }
                    }
                    StatementKind::StorageLive(..) => debug!("Kind: StorageLive"),
                    StatementKind::StorageDead(..) => debug!("Kind: StorageDead"),
                    _ => debug!("Kind: another"),
                    //StatementKind::FakeRead(..) => debug!("Kind: FakeRead"),
                    //StatementKind::SetDiscriminant { place: _, variant_index: _ } => debug!("Kind: SetDiscriminant"),
                    //StatementKind::Deinit(..) => debug!("Kind: Deinit"),
                    //StatementKind::Retag(..) => debug!("Kind: Retag"),
                    //StatementKind::PlaceMention(..) => debug!("Kind: PlaceMention"),
                    //StatementKind::AscribeUserType(..) => debug!("Kind: AscribeUserType"),
                    //StatementKind::Coverage(..) => debug!("Kind: Coverage"),
                    //StatementKind::Intrinsic(..) => debug!("Kind: Intrinsic"),
                    //StatementKind::ConstEvalCounter => debug!("Kind: ConstEvalCounter"),
                    //StatementKind::Nop => debug!("Kind: Nop"),
                    //StatementKind::BackwardIncompatibleDropHint { place: _, reason: _ } => debug!("Kind: BackwardIncompatibleDropHint"),
                }
                debug!("{:?}", statement);
            }

            debug!("\nTERMINATORS\n");
            // try to ID what to rewrite
            match &block.terminator().kind {
                TerminatorKind::Call {
                    func: operand,
                    args: op_args,
                    ..
                } => {
                    debug!("\nCALL func: {:?}", operand);
                    for (i, arg) in op_args.into_iter().enumerate() { //if op_args.len() > 1 {
                        if i != 0 {
                            continue;
                        }
                        match &arg.node {
                            Operand::Move(place) 
                            | Operand::Copy(place) => {
                                let place_ty = place.ty(local_decls, tcx);
                                debug!("arg type: {:?}", place_ty);
                                let deref = place_ty.ty.builtin_deref(false);
                                if deref.is_some() && deref.unwrap().is_trait() {
                                    debug!("REPLACE");
                                }
                            },
                            Operand::Constant(_) => {},
                        }
                    }
                },
                TerminatorKind::TailCall {
                    func: operand,
                    ..
                } => {
                    // skipping for now
                    debug!("\nTAILCALL func: {:?}", operand);
                },
                _ => debug!("\nanother terminator"),
            }
        }
    }

    fn is_required(&self) -> bool {
        true
    }
}
