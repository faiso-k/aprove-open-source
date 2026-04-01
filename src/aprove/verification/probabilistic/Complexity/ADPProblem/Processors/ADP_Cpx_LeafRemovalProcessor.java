package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Leaf Removal Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_LeafRemovalProcessor extends ADP_Cpx_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem pqdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!pqdp.getInnermost() || !pqdp.isBasic()) {
            return false;
        }
        // Check if there are any leafs in the dependency graph
        final Set<ProbabilisticRule> leafRules = pqdp.getDependencyGraph().getLeafRules();
        if (leafRules.isEmpty()) {
            return false;
        }
        // Check if some leaf contains annotations
        for (final ProbabilisticRule rule : leafRules) {
            if (rule.isADP(pqdp.getDeAnnoMap())) {
                return true;
            }
        }
        return false;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processCpxADPProblem(final ADP_Cpx_Problem origPqdp, final Abortion aborter) throws AbortionException {
        final Set<ProbabilisticRule> leafRules = origPqdp.getDependencyGraph().getLeafRules();

        // We remove leaf rules from P,S,K because we store usable rules in sWithQ
        final ADP_Cpx_Problem newPqdp;
        newPqdp = origPqdp.getSubProblemWithRemovedLeafs(leafRules);

        final boolean innermost = origPqdp.QsupersetOfLhsS();
        final CpxADP_LeafRemovalProof lrProof = new CpxADP_LeafRemovalProof(leafRules);

        return ResultFactory.proved(newPqdp, BothBounds.create(), lrProof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class CpxADP_LeafRemovalProof extends ADP_SAST_Proof {

        private final Set<ProbabilisticRule> leafRules;

        private CpxADP_LeafRemovalProof(final Set<ProbabilisticRule> leafRules) {
            this.leafRules = leafRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            res.append("As part of the dependency graph processor, we may remove all leaf"); // Add Citation;
            res.append(o.linebreak());
            res.append("Leaf rules:");
            res.append(o.linebreak());
            res.append(o.set(this.leafRules, Export_Util.RULES));
            res.append(o.linebreak());
            return o.export(res.toString());
        }
    }
}
