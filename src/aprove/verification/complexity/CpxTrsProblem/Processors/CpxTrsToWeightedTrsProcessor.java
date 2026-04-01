package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms a CpxTrs into a WeightedTrs (where all rules have weight 1)
 * @author mnaaf
 */
public class CpxTrsToWeightedTrsProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    protected Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem obl, final Abortion aborter) {
        Set<WeightedRule> weightedRules = new LinkedHashSet<>();
        for (Rule rule : obl.getR()) {
            weightedRules.add(WeightedRule.create(rule));
        }
        CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(weightedRules),
            obl.getRewriteStrategy() == RewriteStrategy.INNERMOST
            || obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST);
        // for parallel-innermost rewriting, we currently lose the "parallel"
        // part of the strategy in the transformation, and innermost rewriting
        // may have higher complexity than parallel-innermost rewriting
        Implication impl = obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST
                ? UpperBound.create() : BothBounds.create();
        return ResultFactory.proved(res, impl, new TrsToWeightedTrsProof());
    }

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        return Options.certifier == Certifier.NONE
                && (obl.getRewriteStrategy() == RewriteStrategy.FULL
                    || obl.getRewriteStrategy() == RewriteStrategy.INNERMOST
                    || obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST);
    }

    class TrsToWeightedTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Transformed TRS to weighted TRS";
        }

    }
}
