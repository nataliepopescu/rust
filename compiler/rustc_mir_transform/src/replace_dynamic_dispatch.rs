//! This pass replaces dynamically dispatched function calls with a switch statement of equivalent 
//! statically dispatched function calls. 

use tracing::debug; //, instrument};

use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub(super) struct ReplaceDynamicDispatch;

impl<'tcx> crate::MirPass<'tcx> for ReplaceDynamicDispatch {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        sess.mir_opt_level() > 0 && !sess.emit_lifetime_markers()
    }

    //#[instrument(level = "debug", skip(self, _tcx))]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!("ReplaceDynamicDispatch");
        debug!("MIR Phase: {:?}", body.phase);
        debug!("body source: {:?}", body.source);
        // FIXME is there a better way to do this?? (sans clone)
        let binding = body.clone();
        let local_decls = binding.local_decls();
        //let should_replace = |place: &Place<'tcx>| {
        //    let place_ty = place.ty(local_decls, tcx);
        //    debug!("arg type: {:?}", place_ty);
        //    let deref = place_ty.ty.builtin_deref(false);
        //    if deref.is_some() && deref.unwrap().is_trait() {
        //        return true;
        //    }
        //    false
        //};

        for block in body.basic_blocks_mut() {
            match &block.terminator {
                Some(Terminator {
                    kind: TerminatorKind::Call {
                        func: operand,
                        args: op_args,
                        ..
                    }, ..
                }) => {
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

                    /*
                    for arg in op_args {
                        match &arg.node {
                            Operand::Move(place) => {
                                debug!("-MOVE arg: {:?}, {:?}", place.local, place.projection);
                                let place_ty = place.ty(local_decls, tcx);
                                debug!("--argtype: {:?}", place_ty.ty);
                                let deref = place_ty.ty.builtin_deref(false);
                                if deref.is_some() {
                                    let unwrapped = deref.unwrap();
                                    debug!("--DEREF'D argkind: {:?}", unwrapped.kind());
                                    if unwrapped.is_trait() {
                                        debug!("RDD HERE");
                                    }
                                }
                            },
                            Operand::Copy(place) => {
                                debug!("-COPY arg: {:?}", place);
                            },
                            Operand::Constant(const_op) => {
                                debug!("-CONST arg: {:?}", const_op);
                            },
                        }
                    }
                    */

                },
                Some(Terminator {
                    kind: TerminatorKind::TailCall {
                        func: operand,
                        ..
                    }, ..
                }) => {
                    // skipping for now
                    debug!("TAILCALL func: {:?}", operand);
                },
                _ => {}
            }
        }
    }

    fn is_required(&self) -> bool {
        true
    }
}
