package aprove.verification.idpframework.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public class EmptyProblemProcessor extends TIDPProcessor<Result> {

    public EmptyProblemProcessor() {
        super("EmptyProblemProcessor");
    }

    private static final EmptyProblemProof EMPTY_PROBLEM_PROOF = new EmptyProblemProof();

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter)
            throws AbortionException {
        for (final IDPSubGraph subGraph : idp.getSubGraphs()) {
            if (!subGraph.isEmpty()) {
                return ResultFactory.unsuccessful("problem not empty");
            }
        }
        return ResultFactory.proved(EmptyProblemProcessor.EMPTY_PROBLEM_PROOF);
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    public static class EmptyProblemProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Empty problem.";
        }

    }
}
