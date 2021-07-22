//! This pass converts unchecked indexing to checked indexing when the 
//! convert-unchecked-indexing option is specified

use crate::transform::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::TyCtxt;

pub struct ConvertUncheckedIndexing;

impl<'tcx> MirPass<'tcx> for ConvertUncheckedIndexing {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        convert_unchecked_indexing(tcx, body)
    }
}

pub fn convert_unchecked_indexing<'tcx>(_tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    // Store new blocks generated; one new block for every 
    // 'get_unchecked[_mut]' call found
    //let mut new_blocks = Vec::new();

    let _cur_len = body.basic_blocks().len();

    for block in body.basic_blocks_mut() {
        //let terminator = block.terminator_mut();
        match block.terminator {
            Some(Terminator {
                kind: 
                    TerminatorKind::Call {
                        destination: Some((_, ref mut destination)), // FIXME
                        //cleanup,
                        ..
                    },
                //source_info,
                ..
            }) if true => {
                debug!("Destination: {:?}", destination);
            }
            /*if destination contains("get_unchecked") && starts_with("core::") {
                // Turn get_unchecked[_mut] call into get[_mut]
                // Requires mutable terminator OR can just replace current terminator?

                // Add new basic block with the unwrap() call
                let unwrap_block = BasicBlockData {
                    statements: vec![],
                    is_cleanup: false,
                    terminator: Some(Terminator {
                        source_info,
                        kind: TerminatorKind::? (),
                    }),
                };

                let idx = cur_len + new_blocks.len();
                new_blocks.push(unwrap_block);
                *destination = BasicBlock::new(idx);
            }*/
            _ => {} // FIXME what does this do?
        }
    }

    debug!("ran cui pass");

    //debug!("Converted {} N get_unchecked[_mut] calls", new_blocks.len());

    //body.basic_blocks_mut().extend(new_blocks);
}
