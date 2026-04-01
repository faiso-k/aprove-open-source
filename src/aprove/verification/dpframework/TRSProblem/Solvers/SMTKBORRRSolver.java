/**
 * @author thetux
 * @version $Id$
 */

package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;

/**
 * @author thetux
 *
 */
public class SMTKBORRRSolver implements RRRSolver {


    private SMTEngine engine;
    private boolean quasi  = false;
    private boolean status = false;

    public SMTKBORRRSolver(boolean quasi, boolean status, SMTEngine engine) {
        this.engine = engine;
        this.status = status;
        this.quasi  = quasi;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter)
            throws AbortionException {

        KBOSMTSolver solver = new KBOSMTSolver(this.quasi, this.status, this.engine);

        return solver.solve(null, R, aborter);
    }

}
