/*
 * Created on 18.7.2008
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;

public abstract class OTRSProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a OTRS with a non-empty set of rules R
     * @return
     */
    protected abstract Result processOTRS(OTRSProblem R, Abortion aborter, RuntimeInformation rti) throws AbortionException;


    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final OTRSProblem problem = (OTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(OTRSProcessor.rIsEmptyProof);
        } else {
            return this.processOTRS(problem, aborter, rti);
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof OTRSProblem) {
            final OTRSProblem R = (OTRSProblem) o;
            if (R.getR().isEmpty()) {
                return true;
            } else {
                return this.isOTRSApplicable(R);
            }
        }
        return false;
    }

    public abstract boolean isOTRSApplicable(OTRSProblem R);

    private final static QTRSProof rIsEmptyProof = new RisEmptyProof();

    private static final class RisEmptyProof extends QTRSProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("The TRS R is empty. Hence, outermost termination is trivially proven.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
