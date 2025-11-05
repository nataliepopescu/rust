//! This file contains code for the various analysis phases of Verifopt. The collected information
//! will ultimately be used in the ReplaceDynamicDispatch Pass.

#![allow(dead_code)]
#![allow(unused_variables)]

use tracing::debug;

use rustc_middle::mir::*;
use rustc_middle::mir::visit::Visitor;

use rustc_data_structures::fx::{FxHashSet as HashSet};

use crate::verifopt_constraints::{ConstraintMap, MapKey, VarType};

pub(crate) struct FlowInterp<'tcx> {
    cmap: ConstraintMap<'tcx>,
}

impl<'tcx> FlowInterp<'tcx> {
    pub(crate) fn new() -> Self {
        FlowInterp {
            cmap: ConstraintMap::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for FlowInterp<'tcx> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        debug!("for func: {:?}", body.span);
        for (bb, data) in traversal::postorder(body) {
            self.visit_basic_block_data(bb, data);
        }
    }

    fn visit_basic_block_data(
        &mut self,
        block: BasicBlock,
        data: &BasicBlockData<'tcx>,
    ) {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let loc = Location { block, statement_index };
            self.visit_statement(stmt, loc);
        }

        // TODO
        // visit_terminator
    }

    fn visit_statement(
        &mut self,
        statement: &Statement<'tcx>,
        _location: Location
    ) {
        match statement.kind {
            StatementKind::Assign(box (place, ref rvalue)) => {
                debug!("assignment!");
                debug!("place: {:?}", place);
                debug!("rval: {:?}", rvalue);
                let mut set = HashSet::default();
                // TODO how much to evaluate rvalue before storing?
                // FIXME need to clone?
                // Rc for cheaper clone?
                set.insert(rvalue.clone());
                self.cmap.scoped_set(
                    None,
                    MapKey::Place(place),
                    Box::new(VarType::Values(set)),
                );
                debug!("CMAP: {:?}", self.cmap);
            },
            _ => debug!("another statement kind"),
        }
    }
}

