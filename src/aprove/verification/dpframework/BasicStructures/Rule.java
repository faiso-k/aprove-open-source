/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * A rule is standard rewrite rule, i.e.
 * it is a pair of terms where the lhs is not a variable
 * and the variables of the lhs are a superset of the variables in
 * the rhs.
 *
 * Two rules are equal iff they are equal up to
 * a variable renaming. Therefore we store for
 * each rule l -> r its standard representation
 * in     stdL -> stdR.
 *
 * @author thiemann
 */
public final class Rule extends GeneralizedRule
    implements Immutable
{

    /**
     * creates a new rule.
     * Restrictions: stdL is null iff stdR is null
     *   if stdL is given, then stdL -> stdR is the
     *   standard representation of l -> r
     * @param l - a non-variable term
     * @param r - a term with less variables then l
     * @param stdL - null or the lhs of the standard representation of l->r
     * @param stdR - null or the rhs of the standard representation of l->r
     */
    @SuppressWarnings("unused")
    private Rule(final TRSFunctionApplication l, final TRSTerm r, final TRSFunctionApplication stdL, final TRSTerm stdR) {
        super(l, r, stdL, stdR);
        if (Globals.useAssertions) {
            final boolean okay = Rule.checkProperLandR(l, r);
            if (!okay && !Globals.DEBUG_NONE) {
                System.err.println("Rule not proper:");
                System.err.println(l + " -> " + r);
            }
            assert (okay);
        }
    }

    public static boolean checkProperLandR(final TRSFunctionApplication l, final TRSTerm r) {
        return l.getVariables().containsAll(r.getVariables());
    }

    /**
     * creates a new rule
     * @param l
     * @param r
     */
    public static Rule create(final TRSFunctionApplication l, final TRSTerm r) {
        return new Rule(l, r, null, null);
    }

    /**
    * creates a new rule
    * @param l - a non-variable term
    * @param r - a term with less variables then l
    * @param stdL - null or the lhs of the standard representation of l->r
    * @param stdR - null or the rhs of the standard representation of l->r
    */
    public static
        Rule
        create(final TRSFunctionApplication l, final TRSTerm r, final TRSFunctionApplication stdL, final TRSTerm stdR)
    {
        return new Rule(l, r, stdL, stdR);
    }

    public static Rule fromGeneralizedRule(final GeneralizedRule grule) {
        return new Rule(grule.getLeft(), grule.getRight(), grule.stdL, grule.stdR);
    }

    public static Set<Rule> fromGeneralizedRules(final Set<GeneralizedRule> grules) {
        final Set<Rule> rules = new LinkedHashSet<Rule>();
        for (final GeneralizedRule grule : grules) {
            rules.add(Rule.fromGeneralizedRule(grule));
        }
        return rules;
    }

    /**
     * returns a map from defined symbols (of rhss) to corresponding rules. Collapsing rules
     * have null as "defined symbol".
     * @param rules
     */
    public static Map<FunctionSymbol, Set<Rule>> getReversedRuleMap(final Iterable<? extends Rule> rules) {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : rules) {
            final TRSTerm rhs = rule.getRight();
            final FunctionSymbol f = rhs.isVariable() ? null : ((TRSFunctionApplication) rhs).getRootSymbol();

            Set<Rule> fRules = reverseRuleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<Rule>();
                reverseRuleMap.put(f, fRules);
            }
            fRules.add(rule);
        }

        return reverseRuleMap;
    }

    /**
     * converts a set of rules into a rule map where for every defined symbol
     * one can lookup the set of corresponding rules.
     * @param rules
     * @return
     */
    public static Map<FunctionSymbol, Set<Rule>> getRuleMap(final Iterable<? extends Rule> rules) {
        final Map<FunctionSymbol, Set<Rule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : rules) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<Rule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<Rule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        return ruleMap;
    }

    /**
     * computes whether some of the given rules is collapsing
     * @param rules
     * @return
     */
    public static boolean isCollapsing(final Iterable<? extends Rule> rules) {
        for (final Rule rule : rules) {
            if (rule.r.isVariable()) {
                return true;
            }
        }
        return false;
    }

    public static boolean isDuplicating(final Collection<Rule> rules) {
        for (final Rule rule : rules) {
            if (rule.isDuplicating()) {
                return true;
            }
        }
        return false;
    }

    public Rule applySubstitution(final Substitution sigma) {
        return Rule.create(this.getLeft().applySubstitution(sigma), this.getRight().applySubstitution(sigma));
    }

    /**
     * Returns true if the name of every variable in this rule starts with the
     * string prefix.
     *
     * @param prefix
     * @return
     */
    public boolean checkVariablePrefix(final String prefix) {
        for (final TRSVariable v : this.getVariables()) {
            if (!v.getName().startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns the lhs
     */
    @Override
    public TRSFunctionApplication getLeft() {
        return this.l;
    }

    /**
     * returns a the standard representation of this
     * rule where l = stdL and r = stdR.
     * (constant time)
     * @see getWithRenumberedVariables
     */
    @Override
    public Rule getStandardRepresentation() {
        // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
        return new Rule(this.stdL, this.stdR, this.stdL, this.stdR);
    }

    /**
     * returns the set of variables occurring on the rhs but not on the lhs.
     */
    @Override
    public Set<TRSVariable> getUnboundedVariables() {
        return new HashSet<TRSVariable>();
    }

    /**
     * returns the set of variables occurring in this rule
     */
    @Override
    public Set<TRSVariable> getVariables() {
        return this.getLeft().getVariables();
    }

    /**
     * renames the variables with given prefix and
     * numbers starting from STANDARD_NUMBER.
     * E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a)
     *           prefix = x
     *           STANDARD_NUMBER = 0
     *    we obtain  f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * @param prefix
     * @return
     */
    @Override
    public Rule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> numberedLAndInt =
            this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> numberedRAndInt =
            this.r.renumberVariables(map, prefix, numberedLAndInt.y);
        return new Rule(numberedLAndInt.x, numberedRAndInt.x, this.stdL, this.stdR);
    }

    public boolean isDuplicating() {
        final Map<TRSVariable, Integer> countMap = this.getLeft().getVariableCount();
        return !this.getRight().hasLessVariablesThan(countMap);
    }

    /**
     * @returns whether the rule l -> r is equal to its internal
     *  standard representation stdL -> stdR
     */
    public boolean isInStandardRepresentation() {
        if (!this.stdL.equals(this.l)) {
            return false;
        }
        if (!this.stdR.equals(this.r)) {
            return false;
        }
        return true;
    }

    public boolean isNonErasing() {
        return this.getLeft().getVariables().equals(this.getRight().getVariables());
    }

    public Rule renameVariables(final Collection<TRSVariable> forbidden) {
        final aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen =
            new aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator(forbidden);
        final TRSFunctionApplication newLeft = this.getLeft().renameVariables(gen);
        final TRSTerm newRight = this.r.renameVariables(gen);
        return new Rule(newLeft, newRight, this.stdL, this.stdR);
    }

    public Rule replaceAllFunctionSymbols(final Map<FunctionSymbol, FunctionSymbol> replaceMap) {
        final TRSFunctionApplication newLeft = (TRSFunctionApplication) this.getLeft().replaceAllFunctionSymbols(replaceMap);
        final TRSTerm newRight = this.getRight().replaceAllFunctionSymbols(replaceMap);
        return Rule.create(newLeft, newRight);
    }

    public Object toCodish(final FreshNameGenerator vars, final FreshNameGenerator funcs) {
        return "rule("
            + this.getLeft().toTERMPTATION(vars, funcs)
            + ","
            + this.getRight().toTERMPTATION(vars, funcs)
            + ")";
    }

    // ================================================================================
    // Annotated Terms
    // ================================================================================

    /**
     * returns the number of annotations in the rhs of this rule.
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return number of annotations in the rhs
     */
    public int countAnnos(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        var counts = this.getRight().getFunctionSymbolCount();
        int sum = 0;
        for (FunctionSymbol anno: deAnnoMap.keySet()) {
            if (counts.containsKey(anno)) {
                sum += counts.get(anno);
            }
        }
        return sum;
    }
}
