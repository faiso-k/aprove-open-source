package aprove.verification.dpframework.CSDPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * Solver for QCSDP problems using polynomials with negative coefficients.
 * @author Carsten Fuhs
 * @version $Id$
 */
public class QCSDPNegCoeffPoloSolver implements QActiveSolver {

    private BigInteger posRange;
    private BigInteger negRange;
    private Engine engine;
    private DiophantineSATConverter dioSatConv;
    private CSNCHeuristicWrapper interHeuristics;
    private SimplificationMode simplificationMode;
    private boolean stripExponents;

    /**
     * @param range
     * @param posRange
     * @param negRange
     * @param engine
     * @param dioSatConv
     */
    public QCSDPNegCoeffPoloSolver(BigInteger posRange, BigInteger negRange,
            Engine engine, DiophantineSATConverter dioSatConv,
            CSNCHeuristicWrapper interHeuristics,
            SimplificationMode simplificationMode, boolean stripExponents) {
        this.posRange = posRange;
        this.negRange = negRange;
        this.engine = engine;
        this.dioSatConv = dioSatConv;
        this.interHeuristics = interHeuristics;
        this.simplificationMode = simplificationMode;
        this.stripExponents = stripExponents;
    }

    /**
     * Invoke setMu(...) before calling this method.
     */
    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        this.interHeuristics.setP(P);
        this.interHeuristics.setR(R);
        return NegCoeffPoloInterpretation.solve(P, R,
                    this.posRange, this.negRange, allstrict,
                    this.interHeuristics, this.simplificationMode,
                    this.stripExponents, this.dioSatConv,
                    this.engine, false, aborter);
        // param false because we only have to require GE for the usable rules here
    }

    /**
     * @param mu the mu to set
     */
    public void setMu(ReplacementMap mu) {
        this.interHeuristics.setMu(mu);
    }
}
