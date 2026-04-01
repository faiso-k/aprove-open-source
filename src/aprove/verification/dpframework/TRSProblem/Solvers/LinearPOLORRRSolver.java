package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * RRR and RRRMu Solver for LinearPOLO
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class LinearPOLORRRSolver implements RRRSolver, RRRMuSolver {

    protected SMTEngine engine;
    private AFSType afsType;
    private int numBits;

    public LinearPOLORRRSolver(SMTEngine engine, AFSType afsType, int numBits) {
        this.engine = engine;
        this.afsType = afsType;
        this.numBits = numBits;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {

        LinearPOLOSolver solver = new LinearPOLOSolver(this.engine, this.afsType, this.numBits);

        return solver.solve(null, R, aborter);
    }

    @Override
    public boolean isRRRMuApplicable(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRRMu(Set<Rule> R,
            ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu,
            Abortion aborter) throws AbortionException {

        LinearPOLOSolver solver = new LinearPOLOSolver(this.engine, this.afsType, this.numBits);

        return solver.solve(null, R, mu, aborter);
    }

}
