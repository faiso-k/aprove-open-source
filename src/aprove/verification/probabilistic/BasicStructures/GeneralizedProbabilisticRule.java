package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import org.apache.commons.math3.fraction.*;
import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A probabilistic rule is a rewriting rule with probabilistic choice on the right hand side.
 * I.e. a rule that maps a term (which may not be a variable) to a multi-distribution over terms.
 * A generalized probabilistic rule only has the condition that the lhs is not a variable,
 * but there is no restriction on the variables for the rhs.
 *
 * @author Jan-Christoph Kassing
 * @version $Id$
 */
public class GeneralizedProbabilisticRule extends RuleSchema implements
    Immutable,
    HasProbRuleForm {

    // ================================================================================
    // Properties
    // ================================================================================

    /** real lhs */
    protected final TRSFunctionApplication l;

    /** real rhs */
    protected final MultiDistribution<TRSTerm> r;

    /* computed values */
    /**
     * canonicalized lhs with variables in TRSTerm.STANDARD_PREFIX and TRSTerm.STANDARD_NUMBER
     * form
     */
    protected final TRSFunctionApplication stdL;

    /**
     * canonicalized rhs with variables in TRSTerm.STANDARD_PREFIX and TRSTerm.STANDARD_NUMBER
     * form
     */
    protected final MultiDistribution<TRSTerm> stdR;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * Create a new Rule. l and r must not be null and stdL and stdR are either both null or both not null.
     * @param l left hand side
     * @param r right hand side
     * @param stdL canonicalized left hand side
     * @param stdR canonicalized right hand side
     */
    protected GeneralizedProbabilisticRule(
        final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r,
        final TRSFunctionApplication stdL,
        final MultiDistribution<TRSTerm> stdR) {
        this.l = l;
        this.r = r;

        if (Globals.useAssertions) {
            final boolean res = GeneralizedProbabilisticRule.checkProperLandR(l, r);
            assert (res);
            assert ((stdL == null && stdR == null) || (stdL != null && stdR != null));
        }

        if (stdL == null) {
            final ImmutablePair<TRSFunctionApplication, MultiDistribution<TRSTerm>> stdLR = makeStdLR(l, r);

            this.stdL = stdLR.x;
            this.stdR = stdLR.y;
        } else {
            // don't trust the user
            if (Globals.useAssertions) {
                final boolean res = GeneralizedProbabilisticRule.checkProperStd(this.l, stdL, this.r, stdR);
                assert (res);
            }
            this.stdL = stdL;
            this.stdR = stdR;
        }

        this.hashCode = 490321 * this.stdL.hashCode() + 12812 * this.stdR.hashCode() + 312038193;
    }

    /**
     * create a new probabilistic rule
     * @param l the left hand side
     * @param r the right hand side. must be a distribution (not subdistribution).
     * @return the new instance
     */
    public static GeneralizedProbabilisticRule create(final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r) {
        return new GeneralizedProbabilisticRule(l, r, null, null);
    }

    /**
     * create a new probabilistic rule. Only use this variant if you know what you are doing.
     *
     * @see GeneralizedProbabilisticRule#create(TRSFunctionApplication, MultiDistribution)
     */
    public static GeneralizedProbabilisticRule create(final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r,
        final TRSFunctionApplication stdL,
        final MultiDistribution<TRSTerm> stdR) {
        return new GeneralizedProbabilisticRule(l, r, stdL, stdR);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    @Override
    public GeneralizedProbabilisticRule getStandardRepresentation() {
        return GeneralizedProbabilisticRule.create(getLhsInStandardRepresentation(), getRhsInStandardRepresentation());
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return this.l;
    }

    @Override
    public TRSFunctionApplication getLhsInStandardRepresentation() {
        return this.stdL;
    }

    @Override
    public MultiDistribution<TRSTerm> getRight() {
        return this.r;
    }

    @Override
    public MultiDistribution<TRSTerm> getRhsInStandardRepresentation() {
        return this.stdR;
    }

    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<>();
        res.add(this.l);
        res.addAll(this.r.getSupport());
        return res;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<>(this.l.getFunctionSymbols());
        for (final TRSTerm t : this.r.getSupport()) {
            res.addAll(t.getFunctionSymbols());
        }
        return res;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this.l.getRootSymbol();
    }

    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = new LinkedHashSet<>(this.l.getVariables());
        for (final TRSTerm t : this.r.getSupport()) {
            res.addAll(t.getVariables());
        }
        return res;
    }

    public ImmutableSet<TRSVariable> getDuplicatingVariables() {
        final Set<TRSVariable> dupVarSet = new HashSet<>();
        final Map<TRSVariable, Integer> varCountLeft = getLeft().getVariableCount();

        for (final TRSTerm term : getRight().getSupport()) {
            Set<TRSVariable> dupVarSetForTerm = new HashSet<>();
            try {
                dupVarSetForTerm = term.getVariableCount()
                    .entrySet()
                    .stream()
                    .filter(e -> e.getValue() - varCountLeft.get(e.getKey()) > 0)
                    .map(e -> e.getKey())
                    .collect(Collectors.toSet());
            } catch (final Exception e) {
                e.printStackTrace();
            }
            dupVarSet.addAll(dupVarSetForTerm);
        }
        return ImmutableCreator.create(dupVarSet);
    }

    public ImmutableSet<TRSVariable> getDecreasingVariables() {
        final Set<TRSVariable> dupVarSet = new HashSet<>();
        final Map<TRSVariable, Integer> varCountLeft = getLeft().getVariableCount();

        for (final TRSTerm term : getRight().getSupport()) {
            final Set<TRSVariable> dupVarSetForTerm = term.getVariableCount()
                .entrySet()
                .stream()
                .filter(e -> e.getValue() - varCountLeft.get(e.getKey()) < 0)
                .map(e -> e.getKey())
                .collect(Collectors.toSet());
            dupVarSet.addAll(dupVarSetForTerm);
        }
        return ImmutableCreator.create(dupVarSet);
    }

    /**
     * Get a set of rules that simulate the behavior of this probabilistic rule by replacing probabilistic choice
     * with non-determinism, i.e. the set {l -> t | t in supp(r)}
     * If this rule is deterministic, a singleton set is returned and the returned rule is equivalent to this rule.
     * @see GeneralizedProbabilisticRule#isDeterministic()
     * @return a set of rules
     */
    public Set<? extends GeneralizedRule> getNonProbabilisticRepresentation() {
        final Set<GeneralizedRule> res = new LinkedHashSet<>();

        for (final TRSTerm t : this.r.getSupport()) {
            res.add(GeneralizedRule.create(this.l, t));
        }

        return res;
    }

    /**
     * Get a rule with the same lhs as this probabilistic rule, i.e. the rule l -> r_1 for l -> {p_1:r_1,...,p_k:r_k}
     * @return a non-probabilistic rule with the same lhs
     */
    public GeneralizedRule getNonProbabilisticLRepresentation() {
        return GeneralizedRule.create(this.l, this.r.getSupport().iterator().next());
    }

    /**
     * Checks if this rules right hand side distribution chooses a single term with probability 1.
     * If this is true, the non-deterministic representation is equivalent to this rule.
     * @see GeneralizedProbabilisticRule#getNonProbabilisticRepresentation()
     * @return true, if this rule is deterministic.
     */
    public boolean isDeterministic() {
        return this.r.isDeterministic();
    }

    /**
     * Checks if a variable occurs strictly more often in a single term in the support of this rules right hand side
     * than in the left hand side.
     * If this is true, than this rule would be called duplicating.
     * @return true, if this rules is duplicating
     */
    public boolean isDuplicating() {
        return !getDuplicatingVariables().isEmpty();
    }

    /**
     * Checks if a variable occurs strictly less often in a single term in the support of this rules right hand side
     * than in the left hand side.
     * If this is true, than this rule would be called variable occurrence decreasing.
     * @return true, if this rules is variable occurrence decreasing
     */
    public boolean isVariableOccDecreasing() {
        final TRSTerm left = getLeft();
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm right = entry.getKey().getKey();
            if (!right.getVariables().containsAll(left.getVariables())) {
                return true;
            }
            final Map<TRSVariable, Integer> varCountRight = right.getVariableCount();
            final Map<TRSVariable, Integer> varCountLeft = left.getVariableCount();
            for (final TRSVariable var : right.getVariables()) {
                if (varCountRight.get(var) < varCountLeft.get(var)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Checks if each variable occurs only once in the left and each right hand side of this rule.
     * If this is true, than this rule would be linear.
     * @return true, if this rules is left-linear
     */
    public boolean isLinear() {
        return isLeftLinear() && isRightLinear();
    }

    /**
     * Checks if each variable occurs only once in the left hand side of this rule.
     * If this is true, than this rule would be left-linear.
     * @return true, if this rules is left-linear
     */
    public boolean isLeftLinear() {
        return !getLeft().getVariableCount().entrySet().stream().anyMatch(e -> e.getValue() > 1);
    }

    /**
     * Checks if each variable occurs only once in each right hand side of this rule.
     * If this is true, than this rule would be rght-linear.
     * @return true, if this rules is left-linear
     */
    public boolean isRightLinear() {
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm right = entry.getKey().getKey();
            if (right.getVariableCount().entrySet().stream().anyMatch(e -> e.getValue() > 1)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Check that l and r are correct formed for a generalized probabilistic rule
     * (not null and variable condition)
     */
    private static boolean checkProperLandR(final TRSFunctionApplication l, final MultiDistribution<? extends TRSTerm> r) {
        return l != null
            && r != null
            && r.isDistribution();
    }

    // ================================================================================
    // canonicalization
    // ================================================================================

    /**
     * Compute the canonical representation of l and r by renumbering the variables.
     *
     * @param l lhs
     * @param r rhs
     * @return a pair (canonicalized lhs, canonicalized rhs)
     */
    private ImmutablePair<TRSFunctionApplication, MultiDistribution<TRSTerm>> makeStdLR(
        final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt = l.renumberVariables(map,
            TRSTerm.STANDARD_PREFIX,
            TRSTerm.STANDARD_NUMBER);
        final HashMultiSet<Pair<TRSTerm, BigFraction>> stdProbabilityMap = new HashMultiSet<>();
        Integer nextFreeNr = stdLAndInt.y;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            final ImmutablePair<? extends TRSTerm, Integer> stdEAndInt = term.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX,
                nextFreeNr);
            stdProbabilityMap.put(new Pair<>(stdEAndInt.x, prob), amount);
            nextFreeNr = stdEAndInt.y;
        }
        return new ImmutablePair<>(stdLAndInt.x,
            new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation());
    }

    /**
     * Check that stdL and stdR are correct canonicalized versions of l and r.
     *
     * @param l    lhs
     * @param r    rhs
     * @param stdL canonicalized lhs that we want to check
     * @param stdR canonicalized rhs that we want to check
     */
    private static boolean checkProperStd(
        final TRSFunctionApplication l,
        final TRSFunctionApplication stdL,
        final MultiDistribution<TRSTerm> r,
        final MultiDistribution<TRSTerm> stdR) {
        if (stdL == null || stdR == null) {
            return false;
        }
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt = l.renumberVariables(map,
            TRSTerm.STANDARD_PREFIX,
            TRSTerm.STANDARD_NUMBER);
        if (!stdLAndInt.x.equals(stdL)) {
            return false;
        }
        final HashMultiSet<Pair<TRSTerm, BigFraction>> stdProbabilityMap = new HashMultiSet<>();
        Integer nextFreeNr = stdLAndInt.y;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            final ImmutablePair<? extends TRSTerm, Integer> stdEAndInt = term.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX,
                nextFreeNr);
            stdProbabilityMap.put(new Pair<>(stdEAndInt.x, prob), amount);
            nextFreeNr = stdEAndInt.y;
        }
        final MultiDistribution<? extends TRSTerm> stdDist = new MultiDistribution<>(stdProbabilityMap);
        if (!stdDist.equals(stdR)) {
            System.err.println(
                l + " -> " + r + " --- >>> " + stdLAndInt.x + " -> " + stdDist + " -- >> " + stdR + " / " + map);
        }
        return stdDist.equals(stdR);
    }

    /**
     * renames the variables with given prefix and numbers starting from
     * STANDARD_NUMBER. E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a) prefix = x
     * STANDARD_NUMBER = 0 we obtain f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     *
     * @param prefix
     * @return a new generalized probabilistic rule with canonicalized variables
     */
    public GeneralizedProbabilisticRule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt = this.l.renumberVariables(map,
            prefix,
            TRSTerm.STANDARD_NUMBER);
        final HashMultiSet<Pair<TRSTerm, BigFraction>> stdProbabilityMap = new HashMultiSet<>();
        Integer nextFreeNr = stdLAndInt.y;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : this.r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            final ImmutablePair<? extends TRSTerm, Integer> stdEAndInt = term.renumberVariables(map,
                prefix,
                nextFreeNr);
            stdProbabilityMap.put(new Pair<>(stdEAndInt.x, prob), amount);
            nextFreeNr = stdEAndInt.y;
        }
        return new GeneralizedProbabilisticRule(stdLAndInt.x,
            new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation(),
            this.stdL,
            this.stdR);
    }

    // ================================================================================
    // Utility
    // ================================================================================

    /**
     * Two probabilistic rules are considered equal if their canonicalized left hand side and right hand sides are equal.
     */
    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof final GeneralizedProbabilisticRule rule) {
            return this.hashCode == rule.hashCode && this.stdL.equals(rule.stdL) && this.stdR.equals(rule.stdR);
        }
        return false;
    }

    @Override
    public String export(final Export_Util eu) {
        return this.l.export(eu) + " "
            + eu.rightarrow()
            + " "
            + this.r.export(eu);
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    // TODO: How can you compare two rules? What order to we use for this? Why is
    // this necessary?
    @Override
    public int compareTo(final RuleSchema other) {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("Method toDom() is not supported for" + this.getClass().getSimpleName());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("Method toCPF() is not supported for" + this.getClass().getSimpleName());
    }

}
