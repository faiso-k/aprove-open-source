package aprove.verification.oldframework.IntTRS.Ranking;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The main algorithm that tries to find a transition invariant.
 *
 * @author Matthias Hoelzel
 *
 */
public class TransitionInvariantFinder {
    /** Transformed rules from the intTRS. */
    private final List<TransitionRelation> transformedRules;

    /** Transition invariant to be created. */
    private final TransitionInvariant transitionInvariant;

    /** Some aborter! */
    private final Abortion aborter;

    /** Some name generator! */
    private final FreshNameGenerator ng;

    /** Transition relations to be included */
    private LinkedList<TransitionRelation> obligationRelations;

    /** Set of pairs of relations we already checked! */
    private final LinkedHashSet<Pair<TransitionRelation, TransitionRelation>> checked;

    /**
     * Constructor!
     *
     * @param rules
     *            the transformed rules
     * @param gen
     *            some name generator
     * @param abortion
     *            some aborter
     */
    public TransitionInvariantFinder(final List<TransitionRelation> rules,
 final Abortion abortion,
            final FreshNameGenerator gen) {
        this.transformedRules = rules;
        this.aborter = abortion;
        this.transitionInvariant = new TransitionInvariant();
        this.checked = new LinkedHashSet<>();
        this.ng = gen;
    }

    /**
     * Tries to find the transition invariant.
     *
     * @return TransitionInvariant or null instead.
     * @throws AbortionException
     *             can be aborted
     */
    public TransitionInvariant findTransitionInvariant()
            throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Transformed rules:");
            for (final TransitionRelation tr : this.transformedRules) {
                l.logln(tr);
            }
            l.logln();
        }

        if (!this.inductionBase()) {
            return null;
        }

        if (!this.inductionStep()) {
            return null;
        }

        return this.transitionInvariant;
    }

    /**
     * Ensures that the rules are contained in the invariant.
     *
     * @return boolean: true iff successful
     *
     * @throws AbortionException
     *             can be aborted
     */
    private boolean inductionBase() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Induction base case:");
        }

        for (final TransitionRelation tr : this.transformedRules) {
            if (tr.isCertainlyWellFounded()) {
                // If it is certainly well-founded, then we can add it.
                this.transitionInvariant.addRelation(tr);
            } else {
                // Otherwise we have to find a ranking relation, which
                // includes the relation arising from the rule.
                final TransitionRelation ranking = this.findRankingRelation(tr);
                if (ranking == null) {
                    return false;
                } else {
                    this.transitionInvariant.addRelation(ranking);
                }
            }
        }
        return true;
    }

    /**
     * Induction step: The concatenation of the rules and the transition
     * invariant has to be included in the transition invariant.
     *
     * @return boolean: true iff successful
     *
     * @throws AbortionException
     *             can be aborted
     */
    private boolean inductionStep() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Induction step:");
        }

        boolean done;
        do {
            done = true;

            // Lets see what we have to do:
            this.buildObligationRelations();

            // Every relations that have to be checked ..
            while (!this.obligationRelations.isEmpty()) {
                final TransitionRelation obligation = this.obligationRelations
                        .pop();

                if (Globals.DEBUG_MATTHIAS) {
                    final DebugLogger l = DebugLogger.getLogger("ranking");
                    l.logln("Some obligation:");
                    l.logln(obligation);
                }

                // .. should eventually be checked:
                if (obligation.isCertainlyWellFounded()) {
                    // If it is well-founded, then there is no problem, because
                    // we can easily add them to the invariant.
                    this.transitionInvariant.addRelation(obligation);
                    this.markAsChecked(obligation);
                    if (Globals.DEBUG_MATTHIAS) {
                        final DebugLogger l = DebugLogger.getLogger("ranking");
                        l.logln("Obligation is well-founded!");
                    }
                } else {
                    // Otherwise we check if it is already contained:
                    if (this.transitionInvariant.isCertainlySupersetOf(
                            obligation, this.aborter)) {
                        // If yes, then we can forget this relation!
                        this.markAsChecked(obligation);
                        if (Globals.DEBUG_MATTHIAS) {
                            final DebugLogger l = DebugLogger
                                    .getLogger("ranking");
                            l.logln("Obligation is included so there is nothing to do!");
                        }
                    } else {
                        // If no, then we have to find a suitable ranking:
                        if (Globals.DEBUG_MATTHIAS) {
                            final DebugLogger l = DebugLogger
                                    .getLogger("ranking");
                            l.logln("Not included!");
                        }
                        done = false;
                        final TransitionRelation ranking = this
                                .findRankingRelation(obligation);

                        if (ranking == null) {
                            // Unfortunately we could not find any ranking.
                            if (Globals.DEBUG_MATTHIAS) {
                                final DebugLogger l = DebugLogger
                                        .getLogger("ranking");
                                l.logln("Could not find a ranking!");
                                l.logln("Here is the history:");
                                for (final TransitionRelation tr : obligation
                                        .getOriginRelations()) {
                                    l.logln(tr);
                                }
                            }
                            if (!this.repairInduction(obligation)) {
                                return false;
                            }
                        } else {
                            this.transitionInvariant.addRelation(ranking);
                            this.markAsChecked(obligation);
                        }
                    }
                }
            }
        } while (!done);

        return true;
    }

    /**
     * When the induction step fails, i.e. we encountered a relation, that is
     * not included and not "rankable", then we go back to the rules and the
     * concatenation of these instead. This is correct because we do not need to
     * have the whole transitive closure included in the transition invariant.
     *
     * @param obligation
     *            the evil relation
     * @throws AbortionException
     *             can be aborted
     * @return boolean: true iff successful
     */
    private boolean repairInduction(final TransitionRelation obligation)
            throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("Repairing induction:");
        }

        final List<TransitionRelation> history = obligation
                .getOriginRelations();
        assert history.size() == 2 : "Strange history of the current obligation relation!";

        final TransitionRelation oldTElement = history.get(1);
        // Get rid of the evil relation:
        this.transitionInvariant.removeRelation(oldTElement);

        // Concatenate the rules contained by the old T-Element
        final TransitionRelation newRule = oldTElement.concatHistory(this.ng,
                this.aborter);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("ranking");
            l.logln("The new rule is ");
            l.logln(newRule);
        }

        // And rank every possible continuation
        for (final TransitionRelation tr : this.transformedRules) {
            if (tr.mightFormChainWith(newRule)) {
                if (Globals.DEBUG_MATTHIAS) {
                    final DebugLogger l = DebugLogger.getLogger("ranking");
                    l.logln("Consider as continuation:");
                    l.logln(tr);
                }

                // Take the old rules and create some possible continuation:
                final TransitionRelation currentRelation = tr.concat(newRule,
                        this.ng, this.aborter);

                // If the relation is already well-founded or already contained,
                // then there is (almost) nothing to do!
                if (currentRelation.isCertainlyWellFounded()) {
                    this.transitionInvariant.addRelation(currentRelation);
                    continue;
                } else if (this.transitionInvariant.isCertainlySupersetOf(
                        currentRelation, this.aborter)) {
                    if (Globals.DEBUG_MATTHIAS) {
                        final DebugLogger l = DebugLogger.getLogger("ranking");
                        l.logln("Already contained!");
                    }
                    continue;
                }

                // Otherwise we have to find a suitable ranking,
                // which can be put into the invariant.
                final TransitionRelation newTRelation = this
                        .findRankingRelation(currentRelation);
                if (newTRelation == null) {
                    // The induction cannot be repaired!
                    return false;
                } else {
                    this.transitionInvariant.addRelation(newTRelation);
                }
            }
        }

        // Rebuild the obligations relations and continue the induction
        this.buildObligationRelations();
        return true;
    }

    /**
     * Marks the current relation as being checked.
     *
     * @param obligation
     *            TransitionRelation
     */
    private void markAsChecked(final TransitionRelation obligation) {
        final List<TransitionRelation> origin = obligation.getOriginRelations();
        assert origin.size() == 2 : "Invalid origin detected!";
        final Pair<TransitionRelation, TransitionRelation> newPair = new Pair<>(
                origin.get(0), origin.get(1));
        assert !this.checked.contains(newPair) : "Relation was already checked?!?";
        this.checked.add(newPair);
    }

    /**
     * Builds all the relations we have to orient.
     *
     * @throws AbortionException
     *             can be aborted
     */
    private void buildObligationRelations() throws AbortionException {
        this.obligationRelations = new LinkedList<>();
        for (final TransitionRelation rule : this.transformedRules) {
            for (final TransitionRelation invariantRelation : this.transitionInvariant
                    .getRelations()) {
                if (rule.mightFormChainWith(invariantRelation)) {
                    if (invariantRelation instanceof Ranking) {
                        final List<TransitionRelation> origin = invariantRelation
                                .getOriginRelations();
                        assert origin.size() == 1 : "A ranking should only have one ancestor!";
                        final TransitionRelation originRelation = origin.get(0);
                        if (originRelation.equals(rule)) {
                            continue;
                        }
                    }
                    if (this.checked
                            .contains(new Pair<TransitionRelation, TransitionRelation>(
                                    rule, invariantRelation))) {
                        continue;
                    } else {
                        this.obligationRelations.push(rule.concat(
                                invariantRelation, this.ng, this.aborter));
                    }
                } else {
                    this.checked
                            .add(new Pair<TransitionRelation, TransitionRelation>(
                                    rule, invariantRelation));
                }
            }
        }
    }

    /**
     * Finds a well-founded ranking relation containing the obligation relation.
     * It also may return null if it can not find a suitable ranking.
     *
     * @param obligation
     *            TransitionRelation
     * @return another TransitionRelation or null if unsuccessful
     * @throws AbortionException
     *             can be aborted
     */
    private TransitionRelation findRankingRelation(
            final TransitionRelation obligation) throws AbortionException {
        final RankingFinder rf = new RankingFinder(obligation, this.ng,
                this.aborter);
        return rf.findRanking();
    }
}
