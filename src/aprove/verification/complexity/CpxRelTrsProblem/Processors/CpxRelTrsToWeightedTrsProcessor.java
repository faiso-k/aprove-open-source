package aprove.verification.complexity.CpxRelTrsProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms a RelTrs into a WeightedTrs, where rules from R have weight 1
 * and rules from S have weight 0.
 *
 * @author mnaaf
 */
public class CpxRelTrsToWeightedTrsProcessor extends RuntimeComplexityRelTrsProcessor {

    @Override
    protected Result processRuntimeComplexityRelTrs(final RuntimeComplexityRelTrsProblem obl, final Abortion aborter) {
        Set<WeightedRule> weightedRules = new LinkedHashSet<>();
        for (Rule rule : obl.getR()) {
            weightedRules.add(WeightedRule.create(rule,1));
        }
        for (Rule rule : obl.getS()) {
            weightedRules.add(WeightedRule.create(rule,0));
        }
        RewriteStrategy rewriteStrategy = obl.getRewriteStrategy();
        CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(weightedRules),
            rewriteStrategy == RewriteStrategy.INNERMOST || rewriteStrategy == RewriteStrategy.PARALLEL_INNERMOST);
        // Weighted TRSs don't support parallel-innermost atm, so use innermost as
        // the next best rewrite strategy (only sound for upper bounds, but still)
        ComplexityImplication cpxImpl = rewriteStrategy == RewriteStrategy.PARALLEL_INNERMOST
                ? UpperBound.create() : BothBounds.create();
        return ResultFactory.proved(res, cpxImpl, new RelTrsToWeightedTrsProof());
    }

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(final RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE;
    }

    class RelTrsToWeightedTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Transformed relative TRS to weighted TRS";
        }

    }
}
