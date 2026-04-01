package aprove.verification.dpframework.MCSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Handles Monotonicity Constraint Transition Systems.
 *
 * @author fuhs
 */
public abstract class MCSProblemProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process an MSCProblem with a non-empty set of transition rules
     * @return
     */
    protected abstract Result processMCSProblem(MCSProblem mcs, Abortion aborter) throws AbortionException;

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        MCSProblem problem = (MCSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getRules().isEmpty()) {
            return ResultFactory.proved(MCSProblemProcessor.rulesAreEmptyProof);
        } else {
            return this.processMCSProblem(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof MCSProblem) {
            return this.isMCSApplicable((MCSProblem) o);
        }
        return false;
    }

    public abstract boolean isMCSApplicable(MCSProblem mcs);

    private final static Proof rulesAreEmptyProof = new RulesAreEmptyProof();

    private static final class RulesAreEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("The set of rules is empty. Hence, there is no run of non-zero length.");
        }

        public String toBibTeX() {
            return "";
        }
    }
}
