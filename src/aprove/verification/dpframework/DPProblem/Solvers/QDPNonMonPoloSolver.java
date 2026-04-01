package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.*;

/**
 * Solver for finding (reduction pairs based on) non-monotonic
 * polynomial orders to delete some pairs from the P component
 * of a QDP problem.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class QDPNonMonPoloSolver {

    private BigInteger posRange;
    private BigInteger negRange;
    private Engine engine;
    private DiophantineSATConverter dioSatConv;
    private NonMonInterHeuristic interHeuristics;

    /**
     * @param range
     * @param posRange
     * @param negRange
     * @param engine
     * @param dioSatConv
     */
    public QDPNonMonPoloSolver(BigInteger posRange, BigInteger negRange,
            Engine engine, DiophantineSATConverter dioSatConv,
            NonMonInterHeuristic interHeuristics) {
        this.posRange = posRange;
        this.negRange = negRange;
        this.engine = engine;
        this.dioSatConv = dioSatConv;
        this.interHeuristics = interHeuristics;
    }

    public NonMonPOLO solve(QDPProblem qdp, boolean allstrict,
            Abortion aborter) throws AbortionException {
        Set<Rule> P = qdp.getP();
        Set<Rule> R = qdp.getR();
        this.interHeuristics.setPR(P, R);
        return NonMonPoloInterpretation.solve(qdp,
                    this.posRange, this.negRange, allstrict,
                    this.interHeuristics, this.dioSatConv,
                    this.engine, aborter);
    }
}
