package aprove.verification.oldframework.SMT.Solver.SMTInterpol;

import aprove.strategies.Abortions.*;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.*;

/**
 * Convenient callback to use Abortions in SMTInterpol.
 * (Nice design, guys! :))
 *
 * @author fuhs
 */
public class AbortionTerminationRequest implements TerminationRequest {
    /** Delegation target for checking termination requests. */
    private Abortion aborter;

    /**
     * @param aborter will be checked regularly by SMTInterpol
     *  (yay delegation)
     */
    public AbortionTerminationRequest(Abortion aborter) {
        this.aborter = aborter;
    }

    @Override
    public boolean isTerminationRequested() {
        // will throw an AbortionException when the time to terminate
        // has come; we want AProVE's Abortion mechanism to handle
        // the termination request
        this.aborter.checkAbortion();
        return false;
    }
}
