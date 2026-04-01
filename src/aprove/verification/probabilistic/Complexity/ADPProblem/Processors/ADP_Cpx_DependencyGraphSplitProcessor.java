package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import immutables.*;

/**
 * Usable Terms Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_DependencyGraphSplitProcessor extends ADP_Cpx_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem qdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!qdp.getInnermost() || !qdp.isBasic()) {
            return false;
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processCpxADPProblem(final ADP_Cpx_Problem qdp, final Abortion aborter) throws AbortionException {
        final Map<Cycle<ProbabilisticRule>, ProbComplexityDependencyGraph> rcSccs = qdp.getDependencyGraph().getReachingClosedSccs();
        final List<ADP_Cpx_Problem> todos = new ArrayList<>(rcSccs.size());
        for (final Map.Entry<Cycle<ProbabilisticRule>, ProbComplexityDependencyGraph> e : rcSccs.entrySet()) {
            final ProbComplexityDependencyGraph newGraph = e.getValue();
            final Set<ProbabilisticRule> keyObjects = e.getKey().getNodeObjects();
            final Set<ProbabilisticRule> newS = new LinkedHashSet<>(keyObjects);
            newS.retainAll(qdp.getS());

            final ImmutableSet<ProbabilisticRule> newProbabilisticRules = newGraph.getP();
            final Set<ProbabilisticRule> newK = new LinkedHashSet<>(newProbabilisticRules);
            newK.removeAll(keyObjects);
            newK.retainAll(qdp.getS());
            newK.addAll(qdp.getK());
            newK.retainAll(newProbabilisticRules);

            if (!newS.isEmpty()) {
                todos.add(qdp.createSubproblem(
                    newGraph,
                    ImmutableCreator.create(newS),
                    ImmutableCreator.create(newK)));
            }
        }
        if (todos.size() == 1) {
            final ADP_Cpx_Problem todo = todos.get(0);
            if (todo.getP().equals(qdp.getP())
                && todo.getS().equals(qdp.getS())) {
                return ResultFactory.unsuccessful("Graph has only one component");
            }
        }
        return ResultFactory.provedMax(todos, UpperBound.create(), new CpxADP_SCCSplitProof(todos.size()));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class CpxADP_SCCSplitProof extends CpxProof {

        private final int numComponents;

        public CpxADP_SCCSplitProof(final int numComponents) {
            this.numComponents = numComponents;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.escape("As part of the dependency graph processor, "
                + "we can split problem in "
                + this.numComponents
                + " new components.");
        }

    }
}
