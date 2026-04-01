package aprove.verification.dpframework.IDPProblem.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;

/**
 * Base class for ITRS problem processors. Takes care of really simple cases.
 *
 * @author noschinski
 *
 */
public abstract class ITRSProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process an ITRS problem; called after the really simple cases are already
     * handled. For semantics see semantics of {@link Processor#process}
     *
     * @param idp Basic Obligation
     */
    protected abstract Result processITRSProblem(ITRSProblem itrs, Abortion aborter)
        throws AbortionException;


    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        ITRSProblem problem = (ITRSProblem) o; // this cast will succeed (see isApplicable)
        // FIXME: We will probably have some simple abortion cases here
        // (cached, empty, ...) cf. QDPProblemProcessor
        return this.processITRSProblem(problem, aborter);
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof ITRSProblem) {
            return this.isITRSApplicable((ITRSProblem) o);
        }
        return false;
    }

    /**
     * Is the ITRS processor applicable to this itrs?
     *
     * @param idp Problem to check for applicability
     * @return True, iff the processor is applicable
     */
    public abstract boolean isITRSApplicable(ITRSProblem itrs);

}
