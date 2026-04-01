package aprove.verification.oldframework.IntTRS.Ranking;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.Ranking.RankingProcessor.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Finds a transition invariant.
 * @author Matthias Hoelzel
 */
public class RankingWorker {
    /** The current intTRS */
    private final IRSwTProblem intTRS;

    /** The rules in transformed form */
    private final List<TransitionRelation> transformedRules;

    /** Generates some fresh names */
    private final FreshNameGenerator ng;

    /** The transition invariant, we want to construct */
    private TransitionInvariant transitionInvariant;

    /** Some aborter */
    private final Abortion aborter;

    /** The proof we are going to construct! */
    private final RankingProof proof;

    /**
     * Constructor!
     * @param prob current intTRS
     * @param proof some proof
     * @param abortion some aborter
     */
    public RankingWorker(final IRSwTProblem prob,
            final RankingProof rankingProof, final Abortion abortion) {
        this.intTRS = prob;
        this.proof = rankingProof;
        this.aborter = abortion;
        this.ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        this.transformedRules = new LinkedList<>();
    }

    /**
     * Starts the machine.
     * @return true iff successful
     * @throws AbortionException can be aborted
     */
    public boolean work() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Obligation:");
            l.logln(this.intTRS);
            l.logln();
        }

        this.transformRules();
        final boolean result = this.findTransitionInvariant();
        if (result) {
            this.proof.setTransitionInvariant(this.transitionInvariant);
        }

        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.finishLog("ranking");
        }

        return result;
    }

    /**
     * Transforms the rules into transiton relations.
     * @throws AbortionException can be aborted
     */
    private void transformRules() throws AbortionException {
        final RulePreparation rp = new RulePreparation(this.ng);
        final Set<IGeneralizedRule> rules = rp.prepare(this.intTRS.getRules());

        final RuleToTransitionRelation ruleRewriter =
            new RuleToTransitionRelation(this.ng, this.aborter);

        for (final IGeneralizedRule iRule : rules) {
            final TransitionRelation newTR =
                ruleRewriter.ruleToTransitionRelation(iRule, true);

            this.transformedRules.add(newTR);
        }
    }

    /**
     * Finds the transition invariant.
     * @return true iff successful
     * @throws AbortionException can be aborted
     */
    private boolean findTransitionInvariant() throws AbortionException {
        final TransitionInvariantFinder tif =
            new TransitionInvariantFinder(this.transformedRules, this.aborter,
                this.ng);
        this.transitionInvariant = tif.findTransitionInvariant();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Here is our transition invariant:");
            l.logln(this.transitionInvariant);
        }

        return this.transitionInvariant != null;
    }
}
