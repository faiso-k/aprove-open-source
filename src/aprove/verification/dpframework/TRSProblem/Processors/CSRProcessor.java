/*
 * Created on 8.5.2006
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;

public abstract class CSRProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a CSR with a non-empty set of rules R
     * @return
     */
    protected abstract Result processCSR(CSRProblem csr, Abortion aborter) throws AbortionException;


    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final CSRProblem problem = (CSRProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(CSRProcessor.rIsEmptyProof);
        } else {
            return this.processCSR(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof CSRProblem) {
            final CSRProblem csr = (CSRProblem) o;
            if (csr.getR().isEmpty()) {
                return true;
            } else {
                return this.isCSRApplicable(csr);
            }
        }
        return false;
    }

    public abstract boolean isCSRApplicable(CSRProblem csr);

    private final static CSRProof rIsEmptyProof = new RisEmptyProof();

    private static final class RisEmptyProof extends CSRProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("The CSR R is empty. Hence, termination is trivially proven.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
