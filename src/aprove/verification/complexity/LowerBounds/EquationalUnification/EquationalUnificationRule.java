package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;
import java.util.Map.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

/**
 * Rules used for equational unification.
 * @author ffrohn
 */
public interface EquationalUnificationRule {

    static class Result {

        private TRSSubstitution refinement;
        private Optional<UnificationProblem> newProblems;

        private Result(TRSSubstitution refinement, Optional<UnificationProblem> newProblems) {
            this.refinement = refinement;
            this.newProblems = newProblems;
        }

        Result(TRSSubstitution refinement, UnificationProblem newProblems) {
            this(refinement, Optional.of(newProblems));
        }

        Result(UnificationProblem newProblem) {
            this(TRSSubstitution.EMPTY_SUBSTITUTION, newProblem);
        }

        public Result(TRSSubstitution refinement) {
            this(refinement, Optional.<UnificationProblem>empty());
        }

        boolean needsRefinement() {
            return !this.refinement.isEmpty();
        }

        TRSSubstitution getRefinement() {
            return this.refinement;
        }

        boolean hasNewProblems() {
            return this.newProblems.isPresent();
        }

        boolean successful() {
            return true;
        }

        public Result applyVariableRenaming(Map<TRSVariable, TRSVariable> renaming) {
            TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(renaming));
            Map<TRSVariable, TRSTerm> newRefinement = new LinkedHashMap<>();
            for (Entry<TRSVariable, ? extends TRSTerm> e: refinement.toMap().entrySet()) {
                TRSVariable newKey = renaming.containsKey(e.getKey()) ? renaming.get(e.getKey()) : e.getKey();
                newRefinement.put(newKey, e.getValue().applySubstitution(sigma));
            }
            return new Result(TRSSubstitution.create(ImmutableCreator.create(newRefinement)), newProblems.map(x -> x.applySubstitution(sigma)));
        }

        public Result applyConstantRenaming(Map<TRSTerm, TRSTerm> rlMap) {
            Map<TRSVariable, TRSTerm> newRefinement = new LinkedHashMap<>();
            for (Entry<TRSVariable, ? extends TRSTerm> e: refinement.toMap().entrySet()) {
                newRefinement.put(e.getKey(), e.getValue().replaceAll(rlMap));
            }
            return new Result(TRSSubstitution.create(ImmutableCreator.create(newRefinement)), newProblems.map(x -> x.replaceAll(rlMap)));
        }

        public Optional<UnificationProblem> getNewProblem() {
            return newProblems;
        }

    }

    /**
     * Thrown if there is no unifier.
     * @author ffrohn
     */
    @SuppressWarnings("serial")
    public static class NoUnifierException extends Exception {
    }

    /**
     * Apply the rule to the given terms.
     *
     * @param s A term.
     * @param t Another term.
     * @param remainingPairs The remaining pairs of terms that have to be unified.
     * @param equationRules The equations the equational unification algorithm has to regard.
     * @return A substitution that has to be applied in order to use the rule and sets of new pairs. Replacing the pair
     *         processed by this rule with these sets of new pairs results in a set of new unification problems. The
     *         original unification problem is solvable if any of the resulting unification problems is solvable. If the
     *         rule is not applicable, then None is returned.
     */
    Optional<Set<Result>> apply(TRSTerm s, TRSTerm t, UnificationProblem unificationProblem) throws NoUnifierException;

}
