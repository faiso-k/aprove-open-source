package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * Searching for polynomial orders with a negative constant not via
 * approximations(-> HM07, SAT'07), but using an explicit max(p, 0)
 * and the case analysis described in "Maximal Termination" (RTA'08).
 *
 * @author fuhs
 * @version $Id$
 */
public class QDPNegConstPoloSolver extends QDPNegCoeffPoloSolver {

    public QDPNegConstPoloSolver(BigInteger posRange, BigInteger negRange,
            Engine engine, DiophantineSATConverter dioSatConv,
            NCInterHeuristic interHeuristics,
            SimplificationMode simplificationMode, boolean stripExponents) {
        super(posRange, negRange, engine, dioSatConv, interHeuristics,
                simplificationMode, stripExponents);
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        this.interHeuristics.setP(P);
        this.interHeuristics.setR(R);
        return NegConstPoloInterpretation.solve(P, R,
                    this.posRange, this.negRange, allstrict,
                    this.interHeuristics, this.simplificationMode,
                    this.stripExponents, this.dioSatConv,
                    this.engine, aborter);
    }

}
