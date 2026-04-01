package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.runtime.*;
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
public class QDPMaxMinPoloSolver implements QActiveSolver {

    private final BigInteger range;
    private final Engine engine;
    private final DiophantineSATConverter dioSatConv;
    private final MMInterHeuristic interHeuristics;
    private final SimplificationMode simplificationMode;
    private final boolean stripExponents;
    private final boolean useConstAddendInOp;

    /**
     * @param range
     * @param posRange
     * @param negRange
     * @param engine
     * @param dioSatConv
     */
    public QDPMaxMinPoloSolver(final BigInteger range, final Engine engine,
            final DiophantineSATConverter dioSatConv,
            final MMInterHeuristic interHeuristics,
            final SimplificationMode simplificationMode, final boolean stripExponents,
            final boolean useConstAddendInOp) {
        this.range = range;
        this.engine = engine;
        this.dioSatConv = dioSatConv;
        this.interHeuristics = interHeuristics;
        this.simplificationMode = simplificationMode;
        this.stripExponents = stripExponents;
        this.useConstAddendInOp = useConstAddendInOp;
    }

    @Override
    public QActiveOrder solveQActive(final Set<? extends GeneralizedRule> P, final Map<? extends GeneralizedRule, QActiveCondition> R,
            final boolean active, final boolean allstrict, final Abortion aborter) throws AbortionException {
        if (Options.certifier.isCeta()) {
            return null;
        }
        this.interHeuristics.setPR(P, R.keySet());
        return MaxMinPoloInterpretation.solve(P, R,
                    this.range, allstrict,
                    this.interHeuristics, this.simplificationMode,
                    this.stripExponents, this.dioSatConv,
                    this.engine, this.useConstAddendInOp,
                    aborter);
    }
}
