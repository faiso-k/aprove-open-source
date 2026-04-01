package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.*;

/**
 * Non-termination result with a feasible error path which can be repeated infinitely often.
 * @author cryingshadow
 * @version $Id$
 */
public class CooperationNonTerminating extends CooperationResult {

    /**
     * The non-termination witness.
     */
    private final ErrorPath path;

    /**
     * @param er The non-termination witness.
     */
    public CooperationNonTerminating(ErrorPath er) {
        this.path = er;
    }

    /**
     * @return The non-termination witness.
     */
    public ErrorPath getErrorPath() {
        return this.path;
    }

    @Override
    public Result toResult() {
        return ResultFactory.disproved(new SafetyIntTRSPoloRedPairProof(this.path));
    }

    @Override
    public String toString() {
        return "NON-TERMINATING";
    }

}
