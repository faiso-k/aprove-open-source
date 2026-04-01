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
 * QDP Polo processor. Tries to orient all usable rules of P by equivalence,
 * all rules of P non-strictly and at least one rule of P strictly, then
 * deletes the strictly oriented rules from P.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class QDPNegCoeffPoloSolver implements QActiveSolver {

    protected BigInteger posRange;
    protected BigInteger negRange;
    protected Engine engine;
    protected DiophantineSATConverter dioSatConv;
    protected NCInterHeuristic interHeuristics;
    protected SimplificationMode simplificationMode;
    protected boolean stripExponents;


    /**
     * @param range
     * @param posRange
     * @param negRange
     * @param engine
     * @param dioSatConv
     */
    public QDPNegCoeffPoloSolver(BigInteger posRange, BigInteger negRange,
            Engine engine, DiophantineSATConverter dioSatConv,
            NCInterHeuristic interHeuristics,
            SimplificationMode simplificationMode, boolean stripExponents) {
        this.posRange = posRange;
        this.negRange = negRange;
        this.engine = engine;
        this.dioSatConv = dioSatConv;
        this.interHeuristics = interHeuristics;
        this.simplificationMode = simplificationMode;
        this.stripExponents = stripExponents;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        this.interHeuristics.setP(P);
        this.interHeuristics.setR(R);
        return NegCoeffPoloInterpretation.solve(P, R,
                    this.posRange, this.negRange, allstrict,
                    this.interHeuristics, this.simplificationMode,
                    this.stripExponents, this.dioSatConv,
                    this.engine, true, aborter);
        // param true because we have to reuiqre EQ for the usable rules here
    }
}
