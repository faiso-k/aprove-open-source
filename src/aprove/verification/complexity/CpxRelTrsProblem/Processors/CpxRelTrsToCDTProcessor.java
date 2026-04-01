package aprove.verification.complexity.CpxRelTrsProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Processors.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class CpxRelTrsToCDTProcessor extends RuntimeComplexityRelTrsProcessor {

    private boolean upperBoundsOnly;
    private ConfluenceCheck confluenceCheck;

    @ParamsViaArgumentObject
    public CpxRelTrsToCDTProcessor(final Arguments arguments) {
        this.upperBoundsOnly = arguments.upperBoundsOnly;
        this.confluenceCheck = arguments.confluenceCheck;
    }

    @Override
    protected Result processRuntimeComplexityRelTrs(final RuntimeComplexityRelTrsProblem obl, final Abortion aborter) {
        final Set<Rule> allRules = new LinkedHashSet<>();
        allRules.addAll(obl.getS());
        allRules.addAll(obl.getR());
        final Pair<Map<Cdt, Rule>, CdtProblem> mapCdt =
            CdtProblem.create(allRules, obl.getDefinedSymbols(), obl.getS(),
                obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST);
        Implication implication;
        if (this.upperBoundsOnly) {
            implication = UpperBound.create();
        }
        else {
            switch (this.confluenceCheck) {
            case NONE :
                // no confluence check, so no reason why BothBounds should be ok
                implication = UpperBound.create();
                break;
            case NON_OVERLAPPING :
                if (CollectionUtils.isOverlapping(allRules)) {
                    implication = UpperBound.create();
                }
                else {
                    // For innermost rewriting, we have confluence by
                    // [PhD thesis Bernhard Gramlich, Corollary 3.2.2].
                    // For parallel-innermost rewriting:
                    // No overlaps, so we know that reducts of each innermost step
                    // are unique [BaaderNipkow98, Lemma 6.3.9], and each
                    // parallel-innermost step is deterministic (all innermost
                    // redexes are contracted simultaneously). Thus, the rewrite relation
                    // is confluent.
                    implication = BothBounds.create();
                }
                break;
            case ALL_INNERMOST_CRITICAL_OVERLAYS_TRIVIAL :
                if (CollectionUtils.hasNonTrivialInnermostCriticalOverlays(allRules)) {
                    implication = UpperBound.create();
                }
                else {
                    // Confluence! For innermost rewriting, by
                    // [PhD thesis Bernhard Gramlich, Theorem 3.5.6].
                    // For parallel-innermost rewriting, it holds too.
                    // Details: https://arxiv.org/abs/2305.18250
                    implication = BothBounds.create();
                }
                break;
            default :
                // (Feel free to add more powerful sufficient criteria
                // for confluence - Noschinski, Emmes, Giesl's Theorem 16 allows for
                // arbitrary criteria for confluence, and so does the work on
                // parallel-innermost rewriting.)
                throw new RuntimeException("Unknown ConfluenceCheck " + this.confluenceCheck);
            }
        }
        return ResultFactory.proved(mapCdt.y, implication, new CpxTrsToCdtProcessor.CpxTrsToCdtProof(
            mapCdt.x,
            mapCdt.y,
            obl.getRewriteStrategy()));
    }

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(final RuntimeComplexityRelTrsProblem obl) {
        return obl.getRewriteStrategy() == RewriteStrategy.INNERMOST
                || obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST;
    }

    public static enum ConfluenceCheck {
        NONE, // confluence check that always says false
        NON_OVERLAPPING, // checks for non-overlappingness
        ALL_INNERMOST_CRITICAL_OVERLAYS_TRIVIAL; // checks whether all innermost critical overlays are trivial
    }

    public static class Arguments {
        // true:  always use UpperBound as implication;
        // false: try to use sufficient criteria to prove confluence,
        //        and if successful, use BothBounds
        public boolean upperBoundsOnly = true;

        public ConfluenceCheck confluenceCheck =
                ConfluenceCheck.ALL_INNERMOST_CRITICAL_OVERLAYS_TRIVIAL;
    }
}
