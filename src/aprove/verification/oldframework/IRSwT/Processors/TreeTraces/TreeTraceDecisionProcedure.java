package aprove.verification.oldframework.IRSwT.Processors.TreeTraces;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Logic.*;

/**
 * This class contains a decision procedure for
 * the termination problem of tree traces.
 * @author Matthias Hoelzel
 */
public class TreeTraceDecisionProcedure {
    /**
     * The given input tree trace.
     */
    private final TreeTrace tt;

    /**
     * The result of this decision procedure.
     * Will either be
     * - YES for termination or
     * - NO  for non-termination or
     * - null when not yet computed.
     */
    private YNM result;

    /**
     * Maps the rules to terms which are reached from its right sides.
     */
    private LinkedHashMap<IGeneralizedRule, LinkedHashSet<TRSTerm>> currentTerms;

    /**
     * Constructor!
     * @param inputTrace the given input tree trace
     */
    public TreeTraceDecisionProcedure(final TreeTrace inputTrace) {
        this.tt = inputTrace;
    }

    /**
     * Runs the algorithm.
     * @return YES or NO, but not MAYBE!
     */
    public YNM decideTermination() {
        // 0. Already done?
        if (this.result != null) {
            return this.result;
        }

        // 1. Initialize data structures:
        this.initialize();

        // 2. Run the simulation steps, until
        //    the result is obtained:
        while (!this.obtainedResult()) {
            this.nextStep();
        }

        this.currentTerms = null;
        return this.result;
    }

    /**
     * Initializes the required data structures.
     * Can also directly conclude non-termination in some
     * trivial cases.
     */
    private void initialize() {
        this.currentTerms = new LinkedHashMap<>();
        for (final IGeneralizedRule rule : this.tt.getRules()) {
            final LinkedHashSet<TRSTerm> termSet = new LinkedHashSet<>();
            termSet.add(rule.getRight());
            this.currentTerms.put(rule, termSet);

            if (rule.getLeft().getMatcher(rule.getRight()) != null) {
                this.result = YNM.NO;
                break;
            }
        }
    }

    /**
     * Concludes termination, if that is possible.
     * After that it will return true, iff the desired result has been computed!
     * @return true or false
     */
    private boolean obtainedResult() {
        if (this.result != null) {
            return true;
        }

        for (final LinkedHashSet<TRSTerm> terms : this.currentTerms.values()) {
            if (!terms.isEmpty()) {
                return false;
            }
        }

        this.result = YNM.YES;
        return true;
    }

    /**
     * Performs one rewriting step. Updates the term in the map "nextTerms".
     * Can conclude non-termination, when it finds a loop.
     */
    private void nextStep() {
        final LinkedHashMap<IGeneralizedRule, LinkedHashSet<TRSTerm>> nextTerms = new LinkedHashMap<>();
        loop: for (final IGeneralizedRule indexRule : this.tt.getRules()) {
            final LinkedHashSet<TRSTerm> terms = this.currentTerms.get(indexRule);
            final LinkedHashSet<TRSTerm> newTerms = new LinkedHashSet<>();
            for (final TRSTerm t : terms) {
                for (final IGeneralizedRule rule : this.tt.getRules()) {
                    final TRSSubstitution sub = rule.getLeft().getMatcher(t);
                    if (sub != null) {
                        final TRSTerm resultTerm = rule.getRight().applySubstitution(sub);
                        newTerms.add(resultTerm);
                        if (indexRule.getLeft().getMatcher(resultTerm) != null) {
                            this.result = YNM.NO;
                            break loop;
                        }
                    }
                }
            }
            nextTerms.put(indexRule, newTerms);
        }
        this.currentTerms = nextTerms;
    }

}
