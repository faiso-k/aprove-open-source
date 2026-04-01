package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import aprove.verification.dpframework.*;

/**
 * Result class.
 * @author marinag, cryingshadow
 */
public abstract class CooperationResult {

    /**
     * @return The result of the analysis together with a proof.
     */
    public abstract Result toResult();

}