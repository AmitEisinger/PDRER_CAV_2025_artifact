// ************************************************************************************************
// use
// ************************************************************************************************

use std::collections::HashSet;
use std::iter;
use fxhash::{FxBuildHasher, FxHashSet};
use super::Frames;
use crate::engines::pdr::PropertyDirectedReachabilitySolver;
use crate::formulas::{Clause, Literal};
use crate::function;
use crate::models::time_stats::function_timer::FunctionTimer;
use crate::solvers::dd::DecisionDiagramManager;

// ************************************************************************************************
// impl
// ************************************************************************************************

impl<T: PropertyDirectedReachabilitySolver, D: DecisionDiagramManager> Frames<T, D> {
    // ********************************************************************************************
    // helper functions
    // ********************************************************************************************

    // MIC method
    fn mic(&mut self, clause: &mut Vec<Literal>, k: usize, d: usize) {
        // iterate over the literals of the original clause
        let literals = clause.clone();
        let mut clause_clone = Vec::with_capacity(clause.len());
        let mut keep : HashSet<Literal, FxBuildHasher> = FxHashSet::default();
        for l in literals {
            if !clause.contains(&l) || keep.contains(&l) {
                continue;
            }
            clause_clone.clear();
            clause_clone.extend(clause.iter().filter(|x1| **x1 != l).copied());
            if self.ctg_down(&mut clause_clone, k, d, &keep) {
                clause.clear();
                clause.extend_from_slice(clause_clone.as_slice())
            } else {
                keep.insert(l);
            }
        }
    }

    // Helper method `ctg_down`
    fn ctg_down(&mut self, clause: &mut Vec<Literal>, k: usize, d: usize, keep: &FxHashSet<Literal>) -> bool {
        if d > self.s.parameters.generalize_using_ctg_max_depth {
            let c = Clause::from_sequence(clause.clone());
            if !self.is_clause_satisfied_by_all_initial_states(&c) {
                return false;
            }

            return match self
                .is_clause_guaranteed_after_transition_if_assumed_and_get_new_lemma(&c, k)
            {
                Some(new_clause) => {
                    *clause = new_clause.unpack().unpack().unpack();
                    true
                }
                None => false,
            };
        }
        let keep_vars = keep.iter().map(|l| l.variable()).collect::<Vec<_>>();
        let mut ctgs = 0;
        loop {
            let c = Clause::from_sequence(clause.clone());
            if !self.is_clause_satisfied_by_all_initial_states(&c) {
                return false;
            }
            let not_c = !c;
            match self.get_predecessor_of_cube(&not_c, k) {
                Err(stronger_cube) => {
                    let mut new_clause = !stronger_cube;
                    let removed_literals = clause
                        .iter()
                        .copied()
                        .filter(|l| !new_clause.contains(l))
                        .collect::<Vec<_>>();
                    if !self
                        .s
                        .fin_state
                        .borrow()
                        .is_clause_satisfied_by_all_initial_states(&new_clause)
                        .is_some_and(|t| t)
                    {
                        let literals_to_add = removed_literals
                            .iter()
                            .find(|x| self.s.fin_state.borrow().is_literal_in_initial_relation(x))
                            .copied();
                        if let Some(lit_to_add) = literals_to_add {
                            new_clause.insert(lit_to_add.to_owned());
                            *clause = new_clause.unpack().unpack().unpack();
                        } else {
                            // Failed to generalize clause, but generalization is still good
                        }
                    }
                    return true;
                }
                Ok((s, _)) => {
                    if d > self.s.parameters.generalize_using_ctg_max_depth {
                        return false;
                    }

                    if clause.iter().any(|x2| {
                        if keep.contains(x2) {
                            let c  =self.solvers.extract_variables_from_solver(k,iter::once(x2.variable()));
                            assert!(c.len() <= 1);
                            if !c.is_empty() && keep.contains(&c.unpack().unpack().unpack()[0]) {
                                return true;
                            }
                        }
                        false
                    }) {
                        self.s.pdr_stats.borrow_mut().note_ctg_theorem_rejection();
                        return false; // Theorem rejection
                    }

                    let keep_projection_in_assignment =  self.solvers.extract_variables_from_solver(k,keep_vars.iter());
                    if keep_projection_in_assignment.iter().any(|x1| {keep.contains(x1)}){
                        return false;
                    }
                  /*  let vars = c.iter().map(|l| l.variable()).collect::<Vec<_>>();
                    let  = self.solvers.extract_variables_from_solver(k,c.iter().map(|lit| lit.variable()).collect());

                    if assignment.iter().any(|l| keep.contains(l)) {
                        return false;
                    }*/

                    let not_s = !s.to_owned();
                    if ctgs < self.s.parameters.generalize_using_ctg_max_ctgs
                        && k > 0
                        && self.is_clause_satisfied_by_all_initial_states(&not_s)
                        && self.is_clause_guaranteed_after_transition_if_assumed(&not_s, k - 1)
                    {
                        ctgs += 1;

                        let mut j = k;
                        while j < self.depth() {
                            if !self.is_clause_guaranteed_after_transition_if_assumed(&not_s, j) {
                                break;
                            }
                            j += 1;
                        }

                        let mut clause_to_add = not_s.unpack().unpack().unpack();
                        self.s
                            .weights
                            .borrow()
                            .sort_literals_by_weights_fast(&mut clause_to_add);
                        self.mic(&mut clause_to_add, j - 1, d + 1);
                        let clause_to_add = Clause::from_sequence(clause_to_add);

                        let de = self.make_delta_element(clause_to_add);
                        self.s
                            .weights
                            .borrow_mut()
                            .update_weights_on_add(de.clause().iter());
                        self.insert_clause_to_highest_frame_possible(de.unpack_clause(), j, true);
                    } else {
                        ctgs = 0;
                        *clause = clause
                            .iter()
                            .filter(|l| not_s.contains(l))
                            .copied()
                            .collect();
                    }
                }
            }
        }
    }

    // ********************************************************************************************
    // API
    // ********************************************************************************************

    /// Implements the generalization algorithm using the Counterexample to Generalization (CTG)
    /// technique.
    pub fn generalize_relative_to_frame_using_ctg(
        &mut self,
        mut clause: Vec<Literal>,
        k: usize,
    ) -> Clause {
        let _timer = FunctionTimer::start(function!(), self.s.time_stats.clone());

        debug_assert!(clause
            .iter()
            .all(|l| self.s.fin_state.borrow().is_state_literal(l)));

        self.mic(&mut clause, k, 1);

        Clause::from_sequence(clause)
    }
}
