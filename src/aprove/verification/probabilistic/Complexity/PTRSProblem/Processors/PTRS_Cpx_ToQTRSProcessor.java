package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * Processor that transforms a PTRS S into its non-probabilistic abstraction np(S).
 * Then we try to analyze termination of np(S) as this implies
 * a finite upper bound on the expected complexity.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_Cpx_ToQTRSProcessor extends PTRS_Cpx_Processor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem ptrs) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processCpxPTRS(final PTRS_Cpx_Problem ptrs, final Abortion aborter)
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

        final CpxPTRS_ToQTRSProof proof = new CpxPTRS_ToQTRSProof();

        final TruthValue finite = ComplexityYNM.createUpper(ComplexityValue.finite());
        return ResultFactory.proved(qtrs, ComplexityIfTerminatingImplication.create(finite), proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class CpxPTRS_ToQTRSProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "A PTRS R is terminating if the TRS NonProb(R) is terminating";
        }
    }
}
