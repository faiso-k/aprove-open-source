package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Leaf Removal Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_LeafRemovalProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem pqdp) {
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
    protected Result processSAST_ADPProblem(final ADP_SAST_Problem origPqdp, final Abortion aborter) throws AbortionException {
        final Set<ProbabilisticRule> leafRules = origPqdp.getDependencyGraph().getLeafRules();

        // We remove leaf rules from P,S,K because we store usable rules in sWithQ
        final ADP_SAST_Problem newPqdp;
        newPqdp = origPqdp.getSubProblemWithRemovedLeafs(leafRules);

        final boolean innermost = origPqdp.QsupersetOfLhsS();
        final SAST_ADPLeafRemovalProof URPproof = new SAST_ADPLeafRemovalProof(leafRules, innermost);

        final Result result = ResultFactory.proved(newPqdp, YNMImplication.EQUIVALENT, URPproof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class SAST_ADPLeafRemovalProof extends ADP_SAST_Proof {

        private final Set<ProbabilisticRule> leafRules;
        private final boolean innermost;

        private SAST_ADPLeafRemovalProof(final Set<ProbabilisticRule> leafRules, final boolean innermost) {
            this.leafRules = leafRules;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.innermost) {
                res.append("We use the leaf removal processor ").append("(Leon's master's thesis)").append(".");
            } else { //full SAST
                res.append("We use the leaf removal processor ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak());
            res.append("All rules that are leafs in the dependency graph, do not contain annotation anymore.");
            res.append(o.linebreak());
            res.append("Leaf rules:");
            res.append(o.linebreak());
            res.append(o.set(this.leafRules, Export_Util.RULES));

            return o.export(res.toString());
        }
    }
}
