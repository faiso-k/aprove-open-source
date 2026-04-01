package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class LinearTransitionPairsSet implements Iterable<LinearTransitionPair> {
    Set<LinearTransitionPair> pairs;

    private LinearTransitionPairsSet(final Set<LinearTransitionPair> pairs) {
        this.pairs = ImmutableCreator.create(pairs);
    }

    public static LinearTransitionPairsSet create(final Collection<LinearTransitionPair> pairs) {
        return new LinearTransitionPairsSet(new HashSet<>(pairs));
    }

    /**
     * TRUE
     */
    public static LinearTransitionPairsSet create() {
        return LinearTransitionPairsSet.create(Arrays.asList(LinearTransitionPair.EMPTY));
    }

    @Override
    public Iterator<LinearTransitionPair> iterator() {
        return this.pairs.iterator();
    }

    @Override
    public String toString() {
        return this.pairs.toString();
    }

    public LinearTransitionPairsSet remove(final LinearTransitionPair tp) {
        final Set<LinearTransitionPair> nPairs = new HashSet<>();
        nPairs.addAll(this.pairs);
        nPairs.remove(tp);

        return LinearTransitionPairsSet.create(nPairs);
    }

    public Set<LinearTransitionPair> getTransitionsPairs() {
        return this.pairs;
    }

    public static LinearTransitionPairsSet create(final LinearDisjunction condition, final PolyRelation rel) {
        final Set<LinearTransitionPair> pairs = new HashSet<>();

        for (final LinearConstraintsSystem c : condition.getLinearConstraintsSystems()) {
            pairs.add(new LinearTransitionPair(c, rel));
        }

        return LinearTransitionPairsSet.create(pairs);
    }

    public Set<IGeneralizedRule> createRules(
        final FunctionSymbol lfSym,
        final FunctionSymbol rfSym,
        final TRSSubstitution sigma)
        {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();

        for (final LinearTransitionPair pair : this.pairs) {
            rules.add(pair.createRule(lfSym, rfSym, sigma));
        }

        return rules;
        }

    public void extendUndefined(final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp) {
        for (final LinearTransitionPair p : this.pairs) {
            p.extandUndefined(varsToFApp);
        }
    }
}
