//! This pass converts unchecked indexing to checked indexing when the 
//! convert-unchecked-indexing option is specified

use crate::transform::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;
//use rustc_middle::ty::FnDef;
//use rustc_index::vec::Idx;
//use rustc_hir::def_id::{DefId, DefIndex};
//use rustc_middle::ty::subst::GenericArg;
//use rustc_middle::ty::List;
//use rustc_middle::ty::Instance;
use rustc_middle::ty::print::with_no_trimmed_paths;
//use rustc_middle::ty::subst::Subst;
use std::fs::OpenOptions;
use std::io::prelude::*;

pub struct ConvertUncheckedIndexing;

impl<'tcx> MirPass<'tcx> for ConvertUncheckedIndexing {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        convert_unchecked_indexing(tcx, body)
    }
}

//#[derive(Debug)]
//struct UnwrapSubsts<'tcx> {
//    immut_u8: &'tcx List<GenericArg<'tcx>>,
//    mut_u8: &'tcx List<GenericArg<'tcx>>,
//}
//
//impl<'tcx> UnwrapSubsts<'tcx> {
//    fn new() -> UnwrapSubsts<'tcx> {
//        UnwrapSubsts {
//            immut_u8: List::empty(),
//            mut_u8: List::empty(),
//        }
//    }
//}

pub fn convert_unchecked_indexing<'tcx>(_tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // Store new blocks generated; one new block for every 'get_unchecked[_mut]' call
    //let mut new_blocks = Vec::new();
    //let mut new_locals = Vec::new();

    //println!();
    //println!("RESTARTING");
    //println!();

    //let mut us = &mut UnwrapSubsts::new();
    //let body_source_def_id = body.source.def_id();
    let (blocks, _) = body.basic_blocks_and_local_decls_mut();
    //let (blocks, locals) = body.basic_blocks_and_local_decls_mut();
    //let blocks_len = blocks.len();
    //let locals_len = locals.len();
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open("/mir-filelist")
        .unwrap();

    for block in blocks.indices() {
        match blocks[block].terminator {
            Some(Terminator {
                kind: 
                    TerminatorKind::Call {
                        ref mut func, 
                        ref args,
                        //destination: Some((ref mut place, ref mut dest_bb)),
                        //ref cleanup,
                        //ref from_hir_call,
                        //ref fn_span,
                        ..
                    },
                ref source_info
            }) => {
                if let Some(constant) = func.constant() {
                    //if let FnDef(old_get_def_id, get_substs) = constant.literal.ty().kind() {
                    let func_string = with_no_trimmed_paths(|| constant.literal.to_string());
                        //println!("get_substs: {:?}", get_substs);

                        //if func_string.starts_with("std::option::Option::") && func_string.ends_with("::unwrap") {
                        //    if func_string.contains("&mut u8") {
                        //            us.mut_u8 = *get_substs;
                        //    } else if func_string.contains("&u8") {
                        //            us.immut_u8 = *get_substs;
                        //    }
                        //}

                    if !func_string.starts_with("core::") || args.len() != 2 || !func_string.contains("get_unchecked") {
                        continue;
                    }

                    if let Err(e) = writeln!(file, "{:?}", source_info.span) {
                        eprintln!("Couldn't write to file: {}", e);
                    }
                        
                    //println!("func_string: {:?}", func_string);
                    //println!("fn_span: {:?}", fn_span);
                    //println!("{:?}", source_info.span);
                    //println!("source_info.scope: {:?}", source_info.scope);

                        //let get_index;
                        //let mut unwrap_substs = us.mut_u8;
                        //if func_string.contains("get_unchecked_mut") {
                        //    get_index = DefIndex::from_u32(10740); // get_mut
                        //    if func_string.contains("u8") {
                        //        unwrap_substs = us.mut_u8;
                        //    }
                        //} else {
                        //    get_index = DefIndex::from_u32(10738); // get
                        //    if func_string.contains("u8") {
                        //        unwrap_substs = us.immut_u8;
                        //    }
                        //}

                        //if unwrap_substs.len() == 0 {
                        //    println!("empty unwrap_substs, continuing...");
                        //    continue;
                        //}

                        //let new_get_def_id = DefId {
                        //    krate: old_get_def_id.krate,
                        //    index: get_index,
                        //};

                        //let unwrap_func = Operand::function_handle(
                        //    tcx, 
                        //    DefId {
                        //        krate: old_get_def_id.krate,
                        //        index: DefIndex::from_u32(7770),
                        //    },
                        //    unwrap_substs, 
                        //    constant.span
                        //);

                        // generate temp local
                        //let local_idx = locals_len + new_locals.len();
                        //let tmp_place : Place<'tcx> = Place::from(Local::from_usize(local_idx));
                        //let param_env = tcx.param_env_reveal_all_normalized(body_source_def_id);
                        //let callee = match Instance::resolve(tcx, param_env, new_get_def_id, get_substs) {
                        //    Ok(it) => match it {
                        //        Some(c) => c, 
                        //        None => {
                        //            println!("no instance?");
                        //            continue;
                        //        },
                        //    },
                        //    Err(e) => {
                        //        println!("error resolving instance: {:?}", e);
                        //        continue;
                        //    }
                        //};
                        //let callee_body = tcx.instance_mir(callee.def);
                        //let callee_body = callee.subst_mir_and_normalize_erasing_regions(
                        //    tcx, 
                        //    param_env, 
                        //    callee_body.clone()
                        //);
                        //new_locals.push(LocalDecl::new(callee_body.return_ty(), source_info.span));

                        // generate new basic block (for unwrap call)
                        //let unwrap_place = place.clone();
                        //let unwrap_dest_bb = dest_bb.clone();
                        //let arg0 = args[0].place().unwrap().local;
                        //let arg1 = args[1].place().unwrap().local;

                        //println!("NEW BLOCK");
                        //println!("unwrap_func: {:?}", unwrap_func);
                        //println!("arg: {:?}", tmp_place);
                        //println!("place: {:?}", unwrap_place);
                        //println!("dest_bb: {:?}", unwrap_dest_bb);
                        //println!();

                        //let unwrap_block = BasicBlockData {
                        //    statements: vec![
                        //        Statement {
                        //            source_info: *source_info,
                        //            kind: StatementKind::StorageDead(arg1),
                        //        },
                        //        Statement {
                        //            source_info: *source_info,
                        //            kind: StatementKind::StorageDead(arg0),
                        //        }
                        //    ],
                        //    is_cleanup: false,
                        //    terminator: Some(Terminator {
                        //        source_info: *source_info,
                        //        kind: TerminatorKind::Call {
                        //            func: unwrap_func,
                        //            args: vec![Operand::Move(tmp_place)],
                        //            destination: Some((unwrap_place, unwrap_dest_bb)),
                        //            cleanup: *cleanup,
                        //            from_hir_call: *from_hir_call,
                        //            fn_span: *fn_span,
                        //        }
                        //    }),
                        //};

                        //let bb_idx = blocks_len + new_blocks.len();
                        //new_blocks.push(unwrap_block);
                        //let new_bb = &BasicBlock::new(bb_idx);

                        //println!("CUR BLOCK: BEFORE");
                        //println!("get_func: {:?}", func);
                        //println!("args: {:?}", args);
                        //println!("place: {:?}", place);
                        //println!("dest_bb: {:?}", dest_bb);
                        //println!();

                        //// replace unchecked terminator with checked terminator
                        //*func = Operand::function_handle(
                        //    tcx, 
                        //    new_get_def_id,
                        //    get_substs, 
                        //    constant.span
                        //);
                        //*place = tmp_place;
                        //*dest_bb = *new_bb;

                        //println!("CUR BLOCK: AFTER");
                        //println!("get_func: {:?}", func);
                        //println!("args: {:?}", args);
                        //println!("place: {:?}", place);
                        //println!("dest_bb: {:?}", dest_bb);
                        //println!();

                        //// insert StorageDead for new tmp_place in destination block
                        //let source_info_clone = source_info.clone();
                        //blocks[unwrap_dest_bb].statements.insert(0, Statement {
                        //    source_info: source_info_clone,
                        //    kind: StatementKind::StorageDead(tmp_place.local),
                        //});

                        //// push StorageLive for new tmp_place in this block
                        //blocks[block].statements.push(Statement {
                        //    source_info: source_info_clone,
                        //    kind: StatementKind::StorageLive(tmp_place.local),
                        //});

                        //println!("inserted StorageDead({:?}) in {:?} bb", tmp_place.local, unwrap_dest_bb);
                        //println!("pushed StorageLive({:?}) in current {:?} bb", tmp_place.local, block);
                        //println!();
                    //}
                }
            },
            _ => {}
        }
    }

    //locals.extend(new_locals);
    //blocks.extend(new_blocks);
}
