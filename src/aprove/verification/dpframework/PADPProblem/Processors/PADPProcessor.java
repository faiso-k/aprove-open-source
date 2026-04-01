package aprove.verification.dpframework.PADPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public abstract class PADPProcessor extends Processor.ProcessorSkeleton {

    /*
     * Process a PADP problem with a non-empty set of rules R
     */
    protected abstract Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException;

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        PADPProblem problem = (PADPProblem) o;
        if (problem.getP().isEmpty()) {
            return ResultFactory.proved(new PADPProcessor.PIsEmptyProof());
        } else {
            return this.processPADP(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        return (o instanceof PADPProblem);
    }

    private static class PIsEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("The set P of dependency pairs is empty.  Thus, there are no (P, R, S, E)-chains.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
