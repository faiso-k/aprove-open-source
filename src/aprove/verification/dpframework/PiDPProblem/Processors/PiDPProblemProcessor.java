/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.PiDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public abstract class PiDPProblemProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a QTRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processPiDPProblem(AbstractPiDPProblem apidp,
        Abortion aborter) throws AbortionException;


    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        AbstractPiDPProblem problem = (AbstractPiDPProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getP().isEmpty()) {
            return ResultFactory.proved(PiDPProblemProcessor.pIsEmptyProof);
        } else {
            return this.processPiDPProblem(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof AbstractPiDPProblem) {
            return this.isPiDPApplicable((AbstractPiDPProblem) o);
        }
        return false;
    }

    public abstract boolean isPiDPApplicable(AbstractPiDPProblem apidp);

    private final static Proof pIsEmptyProof = new PisEmptyProof();

    private static final class PisEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("The TRS P is empty. Hence, there is no (P,R,Pi) chain.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
