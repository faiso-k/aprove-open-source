package aprove.verification.probabilistic.Termination.PTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that transforms a PTRS S into its non-probabilistic abstraction np(S).
 * Then we try to analyze termination of np(S) as this implies SAST, PAST and AST of S.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_ToQTRSProcessor extends PTRS_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter)
        throws AbortionException {
        final Set<Rule> nonPropRules = new HashSet<>();
        for (final ProbabilisticRule pr : ptrs.getProbabilisticRules()) {
            for (final TRSTerm r : pr.getRight().getSupport()) {
                nonPropRules.add(Rule.create(pr.getLeft(), r));
            }
        }

        final Set<TRSFunctionApplication> Q = ptrs.isInnermost() ? CollectionUtils.getLeftHandSides(nonPropRules)
            : new HashSet<>();

        final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(nonPropRules), Q);

        final PTRStoQTRSProof proof = new PTRStoQTRSProof();

        if (ptrs.getTarget() == ProbabilisticTerminationResult.certainTermination) {
            return ResultFactory.proved(qtrs, YNMImplication.EQUIVALENT, proof);
        } else {
            return ResultFactory.proved(qtrs, YNMImplication.SOUND, proof);
        }
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class PTRStoQTRSProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "A PTRS R is terminating if the TRS NonProb(R) is terminating";
        }
    }
}
