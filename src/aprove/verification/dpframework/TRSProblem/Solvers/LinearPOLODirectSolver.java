package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;

/**
 * @author Andreas Kelle-Emden
 *
 */
public class LinearPOLODirectSolver implements DirectSolver {

    private SMTEngine engine;
    private AFSType afsType;
    private int numBits;

    public LinearPOLODirectSolver(SMTEngine engine, AFSType afsType, int numBits) {
        this.engine = engine;
        this.afsType = afsType;
        this.numBits = numBits;
    }

    @Override
    public ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter)
            throws AbortionException {

        LinearPOLOSolver solver = new LinearPOLOSolver(this.engine, this.afsType, this.numBits);

        return solver.solve(Constraint.fromRules(R, OrderRelation.GR), null, aborter);
    }

}
