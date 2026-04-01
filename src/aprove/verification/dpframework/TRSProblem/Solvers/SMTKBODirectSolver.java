package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;

/**
 * @author Andreas Kelle-Emden
 *
 */
public class SMTKBODirectSolver implements DirectSolver {

    private SMTEngine engine;
    private boolean quasi  = false;
    private boolean status = false;

    public SMTKBODirectSolver(boolean quasi, boolean status, SMTEngine engine) {
        this.engine = engine;
        this.status = status;
        this.quasi  = quasi;
    }

    @Override
    public ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter)
            throws AbortionException {

        KBOSMTSolver solver = new KBOSMTSolver(this.quasi, this.status, this.engine);

        return solver.solve(Constraint.fromRules(R, OrderRelation.GR), null, aborter);
    }

}
