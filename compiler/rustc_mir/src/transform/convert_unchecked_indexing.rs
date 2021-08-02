//! This pass converts unchecked indexing to checked indexing when the 
//! convert-unchecked-indexing option is specified

use crate::transform::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt, FnDef};
use rustc_index::vec::Idx;
use rustc_hir::def_id::{DefId, DefIndex};
use rustc_middle::ty::subst::GenericArg;
use rustc_middle::ty::List;

pub struct ConvertUncheckedIndexing;

impl<'tcx> MirPass<'tcx> for ConvertUncheckedIndexing {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        convert_unchecked_indexing(tcx, body)
    }
}

#[derive(Debug)]
struct UnwrapSubsts<'tcx> {
    immut_u8: &'tcx List<GenericArg<'tcx>>,
    mut_u8: &'tcx List<GenericArg<'tcx>>,
    immut_u32: &'tcx List<GenericArg<'tcx>>,
    mut_u32: &'tcx List<GenericArg<'tcx>>,
}

pub fn convert_unchecked_indexing<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // Store new blocks generated; one new block for every 'get_unchecked[_mut]' call
    //let mut new_blocks = Vec::new();
    //let mut new_locals = Vec::new();

    println!();
    println!("RESTARTING");
    println!();

    let mut us = &mut UnwrapSubsts {
        immut_u8: List::empty(),
        mut_u8: List::empty(),
        immut_u32: List::empty(),
        mut_u32: List::empty(),
    };
    println!("unwrap_substs struct??: {:?}", us);

    let (blocks, locals) = body.basic_blocks_and_local_decls_mut();
    let blocks_len = blocks.len();
    let locals_len = locals.len();

    for block in blocks {
        match block.terminator {
            Some(Terminator {
                kind: 
                    TerminatorKind::Call {
                        // func: Operand<'tcx>
                        //   example: core::slice::<impl [u32]>::get_unchecked::<usize>
                        ref mut func, 
                        // ConstantKind::Ty(&'tcx ty::Const<'tcx>)
                        // ConstantKind::Ty(ty::Const::?)
                        //   Const { Ty, ConstKind }
                        //: Operand::Constant(box Constant {
                            //literal,
                            //span,
                            //user_ty,
                        //}),
                        // args: Vec<Operand<'tcx>>
                        //   example: move _3
                        ref args,
                        // destination: Option<(Place<'tcx>, BasicBlock)>
                        //   example place: _15
                        //   example dest_bb: bb8
                        destination: Some((ref mut place, ref mut dest_bb)),
                        ..
                        //ref cleanup,
                        //ref from_hir_call,
                        //ref fn_span,
                    },
                //ref source_info
                ..
            }) => {
                // FnDef(DefId, SubstsRef<'tcx>)
                // pub type SubstsRef<'tcx> = &'tcx InternalSubsts<'tcx>;
                // pub type InternalSubsts<'tcx> = List<GenericArg<'tcx>>;
                // pub struct GenericArg { ptr: NonZeroUsize, marker: PhantomData<(...)> }
                if let Some(constant) = func.constant() {
                    if let FnDef(old_get_def_id, get_substs) = constant.literal.ty().kind() {
                        let func_string = constant.literal.to_string();
                        println!("func_string: {:?}", func_string);
                        println!("get_substs: {:?}", get_substs);

                        // FIXME can also do .. get_substs.type_at(0);

                        // eventually make switch statement
                        if func_string.starts_with("Option::") && func_string.ends_with("::unwrap") {
                            if func_string.contains("&mut u8") {
                                    us.mut_u8 = *get_substs;
                                    println!("setting mut_u8: {:?}", us.mut_u8);
                            } else if func_string.contains("&u8") {
                                    us.immut_u8 = *get_substs;
                                    println!("setting immut_u8: {:?}", us.immut_u8);
                            } else if func_string.contains("&mut u32") {
                                    us.mut_u32 = *get_substs;
                                    println!("setting mut_u32: {:?}", us.mut_u32);
                            } else if func_string.contains("&u32") {
                                    us.immut_u32 = *get_substs;
                                    println!("setting immut_u32: {:?}", us.immut_u32);
                            }
                        }

                        if !func_string.starts_with("core::") || args.len() != 2 || !func_string.contains("get_unchecked") {
                            continue;
                        }

                        println!();

                        let get_index;
                        let mut unwrap_substs = us.mut_u8;
                        if func_string.contains("get_unchecked_mut") {
                            get_index = DefIndex::from_u32(10740); // get_mut
                            if func_string.contains("u8") {
                                unwrap_substs = us.mut_u8;
                                println!("getting mut_u8: {:?}", us.mut_u8);
                                println!();
                            } else if func_string.contains("u32") {
                                unwrap_substs = us.mut_u32;
                                println!("getting mut_u32: {:?}", us.mut_u32);
                                println!();
                            }
                        } else {
                            get_index = DefIndex::from_u32(10738); // get
                            if func_string.contains("u8") {
                                unwrap_substs = us.immut_u8;
                                println!("getting immut_u8: {:?}", us.immut_u8);
                                println!();
                            } else if func_string.contains("u32") {
                                unwrap_substs = us.immut_u32;
                                println!("getting immut_u32: {:?}", us.immut_u32);
                                println!();
                            }
                        }

                        if unwrap_substs.len() == 0 {
                            println!("empty unwrap_substs");
                            continue;
                        }

                        let new_get_def_id = DefId {
                            krate: old_get_def_id.krate,
                            index: get_index,
                        };
                        let new_unwrap_def_id = DefId {
                            krate: old_get_def_id.krate,
                            index: DefIndex::from_u32(7770),
                        };

                        //let new_unwrap_def = FnDef(new_unwrap_def_id, unwrap_substs);
                        println!("unwrap_substs: {:?}", unwrap_substs);
                        let unwrap_func = Operand::function_handle(tcx, new_unwrap_def_id, unwrap_substs, constant.span);

                        println!("old_get_def_id: {:?}", old_get_def_id);
                        println!("new_get_def_id: {:?}", new_get_def_id);
                        println!("unwrap_func: {:?}", unwrap_func);

                        // generate temp local
                        let local_idx = locals_len; // + new_locals.len();
                        let tmp : Place<'tcx> = Place::from(Local::from_usize(local_idx));
                        //new_locals.push(LocalDecl::new(tmp, constant.span));

                        // generate new basic block (for unwrap call)
                        let unwrap_place = place.clone();
                        let unwrap_dest_bb = dest_bb.clone();

                        let arg0 = args[0].place().unwrap().local;
                        let arg1 = args[1].place().unwrap().local;

                        println!("arg to unwrap: {:?}", tmp);
                        println!("destination of unwrap: {:?}", unwrap_dest_bb);
                        println!("lval place of unwrap: {:?}", unwrap_place);

                        //let unwrap_block = BasicBlockData {
                        //    statements: vec![
                        //        Statement {
                        //            *source_info,
                        //            kind: StatementKind::StorageDead(arg1),
                        //        },
                        //        Statement {
                        //            *source_info,
                        //            kind: StatementKind::StorageDead(arg0),
                        //        }
                        //    ],
                        //    is_cleanup: false,
                        //    terminator: Some(Terminator {
                        //        *source_info,
                        //        kind: TerminatorKind::Call {
                        //            func: unwrap_func,
                        //            args: vec![Operand::Move(tmp)],
                        //            destination: Some(unwrap_place, unwrap_dest_bb),
                        //            cleanup: *cleanup,
                        //            from_hir_call: *from_hir_call,
                        //            fn_span: *fn_span,
                        //        }
                        //    }),
                        //};

                        let bb_idx = blocks_len; // + new_blocks.len();
                        //new_blocks.push(unwrap_block);
                        let new_bb = &BasicBlock::new(bb_idx);

                        println!("args to new call: {:?}, {:?}", arg0, arg1);
                        println!("destination of new call: {:?}", new_bb);
                        println!("lval place of new call: {:?}", tmp);

                        println!("BEFORE");
                        println!("func: {:?}", func);
                        println!("place: {:?}", place);
                        println!("dest_bb: {:?}", dest_bb);

                        // replace unchecked terminator with checked terminator
                        *func = Operand::function_handle(tcx, new_get_def_id, get_substs, constant.span);
                        *place = tmp;
                        *dest_bb = *new_bb;

                        println!("AFTER");
                        println!("func: {:?}", func);
                        println!("place: {:?}", place);
                        println!("dest_bb: {:?}", dest_bb);
                        println!();
                    }
                }
            },
            _ => {}
        }
    }

    //body.local_decls.extend(new_locals);
    //body.basic_blocks_mut().extend(new_blocks);
}
