/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public abstract class PiTRSProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a PiTRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processPiTRS(AbstractPiTRSProblem apitrs,
        Abortion aborter) throws AbortionException;


    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        AbstractPiTRSProblem problem = (AbstractPiTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(PiTRSProcessor.rIsEmptyProof);
        } else {
            return this.processPiTRS(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof AbstractPiTRSProblem) {
            return this.isPiTRSApplicable((AbstractPiTRSProblem) o);
        }
        return false;
    }

    public abstract boolean isPiTRSApplicable(AbstractPiTRSProblem apitrs);

    private final static Proof rIsEmptyProof = new RisEmptyProof();

    private static final class RisEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("The TRS R is empty. Hence, termination is trivially proven.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
