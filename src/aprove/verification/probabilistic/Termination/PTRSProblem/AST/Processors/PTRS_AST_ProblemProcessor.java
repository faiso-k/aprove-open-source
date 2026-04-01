package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import aprove.cli.ObligationCache.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class PTRS_AST_ProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof final PTRSProblem ptrs) {
            if (ptrs.getTarget() != ProbabilisticTerminationResult.AST) {
                return false;
            }

            if (ptrs.getPR().isEmpty()) {
                return true;
            } else {
                return isPTRSApplicable(ptrs);
            }
        }
        return false;
    }

    /**
     * Check whether this processor is applicable to the PTRSProblem
     * @return
     */
    public abstract boolean isPTRSApplicable(PTRSProblem R);

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException {
        final PTRSProblem problem = (PTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getPR().isEmpty()) {
            return ResultFactory.proved(new RisEmptyProof(problem.getRewriteStrategy(), problem.getTarget()));
        }
        if (BasicObligationCache.oblCache != null) {
            final YNM value = (YNM) BasicObligationCache.oblCache.lookup(problem);
            if (value != null) {
                switch (value) {
                    case YES:
                        return ResultFactory.proved(PTRS_AST_ProblemProcessor.pIsCachedProof);
                    case NO:
                        return ResultFactory.disproved(PTRS_AST_ProblemProcessor.pIsCachedProof);
                    default:
                        break;
                }
            }
            oblNode.addTruthValueListener(
                new BasicObligationCache.CacheTruthValueListener(BasicObligationCache.oblCache, o));
        }
        return processPTRSProblem(problem, aborter);
    }

    /**
     * Process a PTRS with a non-empty set of rules
     * @return
     */
    protected abstract Result processPTRSProblem(PTRSProblem R, Abortion aborter) throws AbortionException;

    // ================================================================================
    // Predefined Proofs
    // ================================================================================

    private static final class RisEmptyProof extends Proof {

        private RewriteStrategy strat;

        public RisEmptyProof(final RewriteStrategy strat, final ProbabilisticTerminationResult target) {
            super();
            this.strat = strat;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder("The PTRS is empty. Hence, ");
            switch (this.strat) {
                case FULL -> res.append("");
                case INNERMOST -> res.append("innermost");
                case OUTERMOST -> res.append("outermost");
                case PARALLEL_INNERMOST -> res.append("parallel innermost");
                case PARALLEL_SIMULTANEOUS -> res.append("parallel simultaneous");
                case PARALLEL_SIMULTANEOUS_INNERMOST -> res.append("parallel simultaneous innermost");
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> res.append("parallel simultanous outermost");
                default -> res.append("");
            }
            res.append(" AST is trivially proven.");
            return o.export(res.toString());
        }

    }

    private final static Proof pIsCachedProof = new PisCachedProof();

    private static final class PisCachedProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return o.export("This PTRS problem has been analyzed before.");
        }

    }

}
