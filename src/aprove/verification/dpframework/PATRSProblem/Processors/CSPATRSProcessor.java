package aprove.verification.dpframework.PATRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public abstract class CSPATRSProcessor extends Processor.ProcessorSkeleton {

    /*
     * Process a CSPATRS with a non-empty set of rules R
     */
    protected abstract Result processCSPATRS(CSPATRSProblem patrs, Abortion aborter) throws AbortionException;

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CSPATRSProblem problem = (CSPATRSProblem) o;
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(new CSPATRSProcessor.RIsEmptyProof());
        } else {
            return this.processCSPATRS(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        return (o instanceof CSPATRSProblem);
    }

    private static class RIsEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("Since R is empty we are done.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
