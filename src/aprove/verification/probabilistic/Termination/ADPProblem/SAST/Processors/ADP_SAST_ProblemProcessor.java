package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

import org.w3c.dom.*;

import aprove.cli.ObligationCache.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * General skeleton of an arbitrary SAST_ADP processor.
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public abstract class ADP_SAST_ProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof ADP_SAST_Problem) {
            return isSAST_ADPApplicable((ADP_SAST_Problem) o);
        }
        return false;
    }

    /**
     * Check whether this processor is applicable to the PQDPProblem
     * @return
     */
    public abstract boolean isSAST_ADPApplicable(ADP_SAST_Problem posQDT);

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation o,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        final ADP_SAST_Problem problem = (ADP_SAST_Problem) o; // this cast will succeed (see isApplicable)
        if (problem.getS().isEmpty()) {
            return ResultFactory.proved(ADP_SAST_ProblemProcessor.sIsEmptyProof);
        }
        if (BasicObligationCache.oblCache != null) {
            final YNM value = (YNM) BasicObligationCache.oblCache.lookup(problem);
            if (value != null) {
                switch (value) {
                    case YES:
                        return ResultFactory.proved(ADP_SAST_ProblemProcessor.pIsCachedProof);
                    case NO:
                        return ResultFactory.disproved(ADP_SAST_ProblemProcessor.pIsCachedProof);
                    default:
                        break;
                }
            }
            oblNode.addTruthValueListener(
                new BasicObligationCache.CacheTruthValueListener(BasicObligationCache.oblCache, o));
        }
        return processSAST_ADPProblem(problem, aborter);
    }

    /**
     * Process a PQDPProblem with a non-empty set of dependency pairs
     * @return
     */
    protected abstract Result processSAST_ADPProblem(ADP_SAST_Problem posQDT, Abortion aborter) throws AbortionException;

    // ================================================================================
    // Predefined Proofs
    // ================================================================================

    final static SisEmptyProof sIsEmptyProof = new SisEmptyProof();

    private static final class SisEmptyProof extends ADP_SAST_Proof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            res.append("S contains no annotations anymore. Hence, there exists no P-CT with infinitely many S-Nodes.");
            res.append(o.linebreak());
            return o.export(res.toString());
        }

        @Override
        public Element toCPF(final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus) {
            return CPFTag.DP_PROOF.create(doc,
                CPFTag.S_IS_EMPTY.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    private final static Proof pIsCachedProof = new PisCachedProof();

    private static final class PisCachedProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return o.export("This probabilistic ADP problem has been analyzed before.");
        }

    }

}
