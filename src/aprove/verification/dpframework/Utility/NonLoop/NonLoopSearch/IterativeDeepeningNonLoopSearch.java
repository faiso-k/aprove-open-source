package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics.NarrowingHeuristic.*;
import aprove.verification.dpframework.Utility.NonLoop.heuristic.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class IterativeDeepeningNonLoopSearch implements NonLoopSearch {

    /**
     * The problem to work on
     */
    private final QDPProblem qdp;

    /**
     * checker for processor abortion
     */
    private final Abortion aborter;

    /**
     * logger to be used
     */
    private final Logger log;

    /**
     * Number of narrowings steps in pre-processing
     */
    private final int narrowing;

    /** cached heuristic **/
    /**
     * Flag to indicate if forward narrowing should be used
     */
    private final boolean forwardNarrowing;

    /**
     * Flag to indicate if backward narrowing should be used
     */
    private final boolean backwardNarrowing;

    /**
     * Flag to indicate if narrowing into variables is permitted
     */
    @SuppressWarnings("unused")
    private final boolean allowVarPos;

    /**
     * The maximum number of iterations done at the moment.
     */
    private final int maxIterations;
    
    /**
     * Set for remembering what PatternRules we have already found to be non-terminating.
     */
    private final Set<ProofedRule> foundProofedRules = new HashSet<ProofedRule>();
    //TODO Do not recompute everything in the second go.
    
     /**
     * Constructor
     *
     * @param qdpArg
     *            The {@link QDPProblem} to investigate.
     * @param aborterArg
     *            An {@link Abortion} to stop the search.
     * @param logArg
     *            A {@link Logger} to log infos.
     * @param heuristic
     *            The {@link NonLoopHeurisitic} to be used.
     */
    public IterativeDeepeningNonLoopSearch(final QDPProblem qdpArg, final Abortion aborterArg, final Logger logArg,
            final NonLoopHeurisitic heuristic) {
        this.qdp = qdpArg;
        this.aborter = aborterArg;
        this.log = logArg;

        NonLoopHeurisitic heuristicToUse;
        if (heuristic != null) {
            heuristicToUse = heuristic;
        } else {
            heuristicToUse = new DefaultNonLoopHeuristic();
        }

        this.narrowing = heuristicToUse.narrowingSteps();
        this.maxIterations = heuristicToUse.maximumIterations();
        this.forwardNarrowing = heuristicToUse.forwardNarrowing();
        this.backwardNarrowing = heuristicToUse.backwardNarrowing();
        this.allowVarPos = heuristicToUse.allowVarPos();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public NonLoopProof findNonLoop() throws AbortionException {

        final Set<ProofedRule> pR = new LinkedHashSet<>();
        final Set<ProofedRule> pRules = new LinkedHashSet<>();

        final Set<ProofedRule> rulesToCheck = new LinkedHashSet<>();
        final Set<ProofedRule> checkedRules = new LinkedHashSet<>();

        final ImmutableSet<Rule> setR = this.qdp.getR();
        final ImmutableSet<Rule> setP = this.qdp.getP();

        // transform every Rule to a TraceableRule
        for (final Rule r : setR) {
            final ProofedRule rule = RuleFromTRS.create(r, setR, setP);
            pR.add(rule);
        }

        for (final Rule r : setP) {
            final ProofedRule rule = RuleFromTRS.create(r, setR, setP);
            rulesToCheck.add(rule);
            pRules.add(rule);
            
            // Start term was not previously returned
            boolean alreadyReturned = false;
            for(ProofedRule foundPR : foundProofedRules) {
                if (foundPR.getPatternRule().getLhs().getInstance(1).getStandardRenumbered()
                        .equals(rule.getPatternRule().getLhs().getInstance(1).getStandardRenumbered())) {
                    alreadyReturned = true;
                }
            }
            if(!alreadyReturned) { // Rule was not previously returned
                final NonLoopProof nlp = NonLoopProofHeuristic.isNonTerminating(rule);
                if (nlp != null) {
                    foundProofedRules.add(rule);
                    return nlp;
                }
            }
        }

        final Set<ProofedRule> toNarrowWith = new LinkedHashSet<>();

        /*** PREPROCESSING ***/

        /** try to get new rules due to instantiating **/
        final Set<ProofedRule> createdByNarrowing = new LinkedHashSet<>();
        for (final Rule dp : setP) {
            createdByNarrowing.addAll(this.creationByNarrowing(dp, setR, setP));
        }

        // union of R and the rules generated above
        final LinkedHashSet<ProofedRule> creations = new LinkedHashSet<>();
        creations.addAll(pR);
        creations.addAll(createdByNarrowing);

        /** narrow in the creations **/
        final Set<ProofedRule> narrowingInR = this.narrowInR(creations, this.narrowing);
        narrowingInR.addAll(pR);

        /** use these narrowings to do Pattern Creation **/
        for (final ProofedRule pr : narrowingInR) {
            toNarrowWith.addAll(PatternCreationHeuristic.findPatterns(pr));
        }

        if (Globals.DEBUG_NEX) {
            System.err.println("\nPreprocessing generated: ");
            for (final ProofedRule rule : toNarrowWith) {
                System.err.println(rule.export(new PLAIN_Util()));
            }
            System.err.println("\n");
        }

        toNarrowWith.addAll(pR);

        Set<ProofedRule> created = new LinkedHashSet<>();

        int iterations = 0;
        while (true) {
            this.aborter.checkAbortion();

            ProofedRule pick;

            if (!rulesToCheck.isEmpty()) {
                // pick and remove first rule of rulesToCheck
                final Iterator<ProofedRule> iter = rulesToCheck.iterator();
                pick = iter.next();
                iter.remove();

                // add to the already checked rules
                checkedRules.add(pick);

                created = new LinkedHashSet<>();

                // narrow with rules from
                created.addAll(this.narrowStep(pick, toNarrowWith, NarrowingDirection.Forward));

                this.aborter.checkAbortion();

                // narrow with rules from P, only at root position
                created.addAll(this.narrowStep(pick, pRules, NarrowingDirection.OnlyRoot));

                this.aborter.checkAbortion();

                // try rewriting to normal forms
                created.addAll(RewritingHeuristic.rewritingHeuristic(pick));

                this.aborter.checkAbortion();

                // check new rules for non-termination
                // note: check only the rules that weren't checked before
                final Set<ProofedRule> toAdd = new LinkedHashSet<>();
                for (final ProofedRule nr : created) {
                    ++iterations;
                    if (this.maxIterations > 0 && iterations > this.maxIterations) {
                        return null;
                    }

                    if (!checkedRules.contains(nr)) {
                        // we only have to add the rules we did not check before
                        toAdd.add(SimplifyMuHeuristic.simplify(nr));

                        // Start term was not previously returned
                        boolean alreadyReturned = false;
                        for(ProofedRule foundPR : foundProofedRules) {
                            if (foundPR.getPatternRule().getLhs().getInstance(1).getStandardRenumbered()
                                    .equals(nr.getPatternRule().getLhs().getInstance(1).getStandardRenumbered())) {
                                alreadyReturned = true;
                            }
                        }
                        if(!alreadyReturned) { // Rule was not previously returned
                            final NonLoopProof nlp = NonLoopProofHeuristic.isNonTerminating(nr);
                            if (nlp != null) {
                                foundProofedRules.add(nr);
                                return nlp;
                            }
                        }
                    }
                }

                // add new rules to currentRules
                rulesToCheck.addAll(toAdd);
            } else {
                this.log.info("No more rules created. => Abort Search!");
                // we can do anything more ... so return null
                return null;
            }
        }
    }

    private Set<ProofedRule> narrowInR(final Set<ProofedRule> R, final int steps) {

        final Set<ProofedRule> resultRules = new LinkedHashSet<>();
        Set<ProofedRule> newRules = new LinkedHashSet<>(R);

        for (int i = 0; i < steps; i++) {
            final Set<ProofedRule> created = new LinkedHashSet<ProofedRule>();

            for (final ProofedRule pr : newRules) {
                created.addAll(this.narrowStep(pr, R, NarrowingDirection.Forward));
            }

            resultRules.addAll(created);
            newRules = new LinkedHashSet<>(created);
        }

        return resultRules;
    }

    private Set<ProofedRule> creationByNarrowing(final Rule dp, final ImmutableSet<Rule> R, final ImmutableSet<Rule> P) {
        final Set<ProofedRule> newRules = new LinkedHashSet<>();

        final TRSTerm rhs = dp.getRight();
        for (final Pair<Position, TRSFunctionApplication> pt : rhs.getNonRootNonVariablePositionsWithSubTerms()) {
            final TRSTerm subr = pt.y;

            for (final Rule r : R) {
                final TRSFunctionApplication lhs = r.getLeft();

                final TRSSubstitution matcher = lhs.getMatcher(subr);
                if (matcher != null) {
                    ProofedRule newRule = RuleFromTRS.create(r, R, P);
                    newRule = Instantiation.create(newRule, matcher);
                    newRules.add(newRule);
                }
            }
        }

        return newRules;
    }

    private Collection<? extends ProofedRule> narrowStep(final ProofedRule pick,
        final Set<ProofedRule> toNarrowWith,
        final NarrowingDirection dir) {

        final Set<ProofedRule> narrowings = new LinkedHashSet<>();

        for (final ProofedRule pr : toNarrowWith) {
            if (this.forwardNarrowing) {
                narrowings.addAll(NarrowingHeuristic.narrowing(pr, pick, dir));
                narrowings.addAll(NarrowingHeuristic.narrowing(pick, pr, dir));
            }
            if (this.backwardNarrowing) {
                narrowings.addAll(NarrowingHeuristic.backwardNarrowing(pick, pr));
                narrowings.addAll(NarrowingHeuristic.backwardNarrowing(pr, pick));
            }
        }

        return narrowings;
    }

    /**
     * Check <tt>toCheck</tt> for already represented {@link PatternRule
     * PatternRules} in <tt>toCheckAgainst</tt>. Already represented
     * {@link ProofedRule ProofedRules} are removed from the {@link Set}
     * <tt>toCheck</tt>.
     *
     * @param toCheck
     *            The {@link PatternRule PatternRules} to check.
     * @param toCheckAgainst
     *            The {@link Set} to check against.
     */
    @SuppressWarnings("unused")
    private void checkAlreadyRepresentedRules(final Set<ProofedRule> toCheck, final Set<ProofedRule> toCheckAgainst) {

        final Set<ProofedRule> toRemove = new LinkedHashSet<ProofedRule>();

        for (final ProofedRule p : toCheck) {
            if (p.getPatternRule().isAlreadyRepresented(toCheckAgainst)) {
                toRemove.add(p);
            }
        }

        toCheck.removeAll(toRemove);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getDescription() {
        return "Iterative Deepning NonLoopSearch";
    }

}
