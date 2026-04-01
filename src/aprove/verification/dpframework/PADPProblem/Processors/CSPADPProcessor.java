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

public abstract class CSPADPProcessor extends Processor.ProcessorSkeleton {

    /*
     * Process a CSPADP problem with a non-empty set of rules R
     */
    protected abstract Result processCSPADP(CSPADPProblem cspadp, Abortion aborter) throws AbortionException;

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CSPADPProblem problem = (CSPADPProblem) o;
        if (problem.getP().isEmpty()) {
            return ResultFactory.proved(new CSPADPProcessor.PIsEmptyProof());
        } else {
            return this.processCSPADP(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        return (o instanceof CSPADPProblem);
    }

    private static class PIsEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("The set P of dependency pairs is empty.  Thus, there are no (P, R, S, E, mu)-chains.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
