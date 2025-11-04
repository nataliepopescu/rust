//! This file contains code for the various analysis phases of Verifopt. The collected information
//! will ultimately be used in the ReplaceDynamicDispatch Pass.

#![allow(unused_variables)]

use tracing::debug;

use rustc_middle::mir::*;
use rustc_middle::mir::visit::Visitor;

pub(crate) struct FlowInterp {}

impl FlowInterp {
    pub(crate) fn new() -> Self {
        FlowInterp {}
    }
}

impl<'tcx> Visitor<'tcx> for FlowInterp {
    fn visit_basic_block_data(
        &mut self,
        block: BasicBlock,
        data: &BasicBlockData<'tcx>,
    ) {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let loc = Location { block, statement_index };
            self.visit_statement(stmt, loc);
        }
    }

    fn visit_statement(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location
    ) {
        match statement.kind {
            StatementKind::Assign(box (place, ref rvalue)) => {
                debug!("assignment!");
                debug!("place: {:?}", place);
                debug!("rval: {:?}", rvalue);
            },
            _ => debug!("another statement kind"),
        }
    }
}

