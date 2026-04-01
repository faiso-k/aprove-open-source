package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;

/**
 * Tries to find an ordering that satisfies l >= r for all rules and l > r for at least one rule.
 *
 * Assumes that the concrete solver used is always applicable.
 * Change isApplicable() if necessary!
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class AbortableRRRSolver implements RRRSolver {

        private SolverFactory factory;

        public AbortableRRRSolver(SolverFactory factory) {
                this.factory = factory;
        }

        /** See above. */
        @Override
        public boolean isRRRApplicable(Set<Rule> R) {
            return true;
        }

        @Override
        public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter) throws AbortionException {
            Set<Constraint<TRSTerm>> cs = Constraint.fromRules(R, OrderRelation.GE);
            for (Constraint<TRSTerm> cons : cs) {
                cons.z = OrderRelation.GR;
                AbortableConstraintSolver<TRSTerm> solver = this.factory.getSolver(cs);
                ExportableOrder<TRSTerm> order = solver.solve(cs, aborter);
                if (order != null) {
                    boolean solved = true;
                    for (Constraint<TRSTerm> c : cs) {
                        if (!order.solves(c)) {
                            solved = false;
                        }
                    }
                    if (solved)
                     {
                        return order; // We have found an ordering where at least one rule can be removed
                    }
                }
                cons.z = OrderRelation.GE;
            }
            return null;
        }

}

