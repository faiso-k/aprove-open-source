package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * General skeleton of an arbitrary SAST_ADP processor.
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public abstract class ADP_Cpx_ProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof ADP_Cpx_Problem) {
            return isCpxADP_Applicable((ADP_Cpx_Problem) o);
        }
        return false;
    }

    /**
     * Check whether this processor is applicable to the PQDPProblem
     * @return
     */
    public abstract boolean isCpxADP_Applicable(ADP_Cpx_Problem posQDT);

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation o,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        final ADP_Cpx_Problem problem = (ADP_Cpx_Problem) o; // this cast will succeed (see isApplicable)
        if (problem.getS().isEmpty()) {
            return ResultFactory.provedWithValue(
                ComplexityYNM.create(
                    ComplexityValue.constant(),
                    ComplexityValue.constant()),
                ADP_Cpx_ProblemProcessor.sIsEmptyProof);
        }
        //Check for cached things.
        return processCpxADPProblem(problem, aborter);
    }

    /**
     * Process a PQDPProblem with a non-empty set of dependency pairs
     * @return
     */
    protected abstract Result processCpxADPProblem(ADP_Cpx_Problem posQDT, Abortion aborter) throws AbortionException;

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
            res.append("Resulting upper bound: O(1)");
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
            return o.export("This ADP problem has been analyzed before.");
        }

    }

}
