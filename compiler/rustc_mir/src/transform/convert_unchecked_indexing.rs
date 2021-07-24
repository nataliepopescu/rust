//! This pass converts unchecked indexing to checked indexing when the 
//! convert-unchecked-indexing option is specified

use crate::transform::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt, FnDef};
use rustc_index::vec::Idx;

pub struct ConvertUncheckedIndexing;

impl<'tcx> MirPass<'tcx> for ConvertUncheckedIndexing {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        convert_unchecked_indexing(tcx, body)
    }
}

pub fn convert_unchecked_indexing<'tcx>(_tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // Store new blocks generated; one new block for every 'get_unchecked[_mut]' call
    //let mut new_blocks = Vec::new();

    let (blocks, locals) = body.basic_blocks_and_local_decls_mut();
    let mut blocks_len = blocks.len();
    let mut locals_len = locals.len();

    for block in blocks {
        let terminator = block.terminator_mut();
        match terminator {
            Terminator {
                kind: 
                    TerminatorKind::Call {
                        // func: Operand<'tcx>
                        //   example: core::slice::<impl [u32]>::get_unchecked::<usize>
                        func: Operand::Constant(box Constant {
                            // ConstantKind::Ty(&'tcx ty::Const<'tcx>)
                            // ConstantKind::Ty(ty::Const::?)
                            //   Const { Ty, ConstKind }
                            literal,
                            //span,
                            ..
                        }),
                        // args: Vec<Operand<'tcx>>
                        //   example: move _3
                        args,
                        // destination: Option<(Place<'tcx>, BasicBlock)>
                        //   example place: _15
                        //   example dest_bb: bb8
                        destination: Some((place, ref dest_bb)),
                        ..
                    },
                //source_info
                ..
            } => {
                // FnDef(DefId, SubstsRef<'tcx>)
                // pub type SubstsRef<'tcx> = &'tcx InternalSubsts<'tcx>;
                // pub type InternalSubsts<'tcx> = List<GenericArg<'tcx>>;
                // pub struct GenericArg { ptr: NonZeroUsize, marker: PhantomData<(...)> }
                if let FnDef(def_id, substs) = *literal.ty().kind() {
                    let mut func_string = literal.to_string();
                    if !func_string.starts_with("core::") || args.len() != 2 || !func_string.contains("get_unchecked") {
                        continue;
                    }

                    println!("def_id.krate.as_usize(): {:?}", def_id.krate.as_usize());
                    println!("def_id.krate.as_u32(): {:?}", def_id.krate.as_u32());

                    println!("def_id.index: {:?}", def_id.index);
                    println!("subst: {:?}", substs);

                    //match def_id {
                    //    DefId {
                    //        krate: CrateNum::Index(CrateId::from_u32(
                    //    },
                    //}

                    if func_string.contains("get_unchecked_mut") {
                        // construct unwrap function name with correct type by matching <impl [_]>
                        if let Some((_, split_string)) = func_string.rsplit_once("<impl [") {
                            if let Some((ty, _)) = split_string.split_once("]") {
                                let unwrap_func = "Option::<&mut [%]>::unwrap".replace("%", ty);

                                // generate temp local
                                locals_len += 1;
                                let local = Local::from_usize(locals_len);
                                let tmp : Place<'tcx> = Place::from(local);

                                // generate new basic block (for unwrap call)
                                let unwrap_place = place.clone();
                                let unwrap_dest_bb = dest_bb.clone();

                                let arg0 = args[0].place().unwrap().local;
                                let arg1 = args[1].place().unwrap().local;

                                println!("unwrap_func: {:?}", unwrap_func);
                                println!("arg to unwrap: {:?}", tmp);
                                println!("destination of unwrap: {:?}", unwrap_dest_bb);
                                println!("lval place of unwrap: {:?}", unwrap_place);

                                //let _unwrap_block = BasicBlockData {
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
                                //            cleanup: None,
                                //            from_hir_call: false,
                                //            fn_span: *span,
                                //        }
                                //    }),
                                //};

                                blocks_len += 1; // TODO remove
                                let bb_idx = blocks_len; // + new_blocks.len();
                                //new_blocks.push(unwrap_block);
                                let new_bb = &BasicBlock::new(bb_idx);

                                // point block to new terminator
                                // ? use function_handle(tcx, def_id, substs, span)
                                // replace unchecked terminator with checked terminator

                                println!("old call: ---{:?}---", func_string);
                                func_string = func_string.replace("_unchecked", "");
                                println!("new call: ---{:?}---", func_string);
                                println!("args to new call: {:?}, {:?}", arg0, arg1);
                                println!("destination of new call: {:?}", new_bb);
                                println!("lval place of new call: {:?}", tmp);
                                //*literal = func_string.replace("_unchecked", "");
                                //*place = tmp;
                                //*dest_bb = new_bb;
                            }
                        } else {
                            println!("no <impl []> ???");
                        }
                    } else {
                        println!("get_unchecked (no mut)");
                    }
                }
            },
            _ => {}
        }
    }

    //body.basic_blocks_mut().extend(new_blocks);
}
