package aprove.verification.complexity.CdtProblem.Processors;

import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Convert (D, S, K, R) to a weighted problem where S gets weight 1, and
 * D \ S as well as R get weight 0.
 * 
 * @author Carsten Fuhs
 */
public class CdtToCpxWeightedTrsProcessor extends CdtProblemProcessor {

    private static final Proof THE_PROOF = new CdtToCpxWeightedTrsProof();

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter) throws AbortionException {
        CpxWeightedTrsProblem newObl = toWeightedTrs(cdtProblem);
        // BothBounds not ok - see comment in CdtToCpxRelTrsProcessor for
        // a counterexample
        Result res = ResultFactory.proved(newObl, UpperBound.create(), THE_PROOF);
        return res;
    }

    /**
     * Converts (D, S, K, R) to S with weight 1 and (D \setminus S) \cup R with
     * weight 0.
     *
     * @param cdtProblem (D, S, K, R); non-null
     * @return S with weight 1 and (D \setminus S) \cup R with weight 0
     */
    private static CpxWeightedTrsProblem toWeightedTrs(CdtProblem cdtProblem) {
        Set<WeightedRule> weightedRules = new LinkedHashSet<>();
        ImmutableSet<Cdt> oldS = cdtProblem.getS();
        ImmutableSet<Cdt> oldTuples = cdtProblem.getTuples();
        Set<Rule> oldR = cdtProblem.getR();

        // generate the weight 1 part ...
        for (Cdt cdt : oldS) {
            weightedRules.add(WeightedRule.create(cdt.getRule(),1));
        }

        // ... then the weight 0 part
        for (Cdt cdt : oldTuples) {
            if (! oldS.contains(cdt)) {
                weightedRules.add(WeightedRule.create(cdt.getRule(),0));
            }
        }
        for (Rule rule : oldR) {
            weightedRules.add(WeightedRule.create(rule,0));
        }

        CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(weightedRules), cdtProblem.isInnermost());
        return res;
    }

    private static class CdtToCpxWeightedTrsProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Converted S to rules of weight 1, and D \\ S as well as R to rules of weight 0.");
        }
    }
}
