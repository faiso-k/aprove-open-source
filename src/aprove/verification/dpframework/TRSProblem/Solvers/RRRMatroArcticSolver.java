package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Wrapper class for RRR solving using a PMatroArcticInt order.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class RRRMatroArcticSolver implements RRRSolver {

    protected final PMatroArcticFactory factory;

    public RRRMatroArcticSolver(final PMatroArcticFactory factory) {
        this.factory = factory;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        // below zero cannot be used for RRR
        if (this.factory.isBelowZero()) {
            return false;
        }

        // and the signature must not have symbols whose arity exceeds 1
        for (Rule rule : R) {
            for (FunctionSymbol fsym : rule.getFunctionSymbols()) {
                if (fsym.getArity() > 1) {
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {
        if (Globals.useAssertions) {
            assert this.isRRRApplicable(R);
        }
        @SuppressWarnings("unchecked") // this cast must always succeed due to the factory method's implementation
        PMatroExoticSolver<ArcticInt> solver = (PMatroExoticSolver<ArcticInt>)this.factory.getQActiveSolver();
        solver.setExtendedMonotone(true);
        Map<Rule, QActiveCondition> emptyRuleSet = Collections.emptyMap();
        return solver.solveQActive(R, emptyRuleSet, false, false, aborter);
    }
}
