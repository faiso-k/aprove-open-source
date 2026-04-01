package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Rip-off of QTermSet for ReducingRHS.
 *
 * @version $Id$
 */
public final class ReduceRHSChecker implements Immutable {

    // a lookup map that determines to each FunctionSymbol the corresponding rules
    // that have this function symbol. Moreover, a distinction between linear and
    // non-linear rules is made (then one can use the faster linearMatch for linear
    // rules)
    private final Map<FunctionSymbol, Pair<LinkedHashSet<Rule>, LinkedHashSet<Rule>>> defSymbolsToRules;

    // the set of all rules
    private final ImmutableSet<Rule> allRules;

    private final boolean isEmpty;

    private final Map<Rule,Boolean> rule2overlap;

    /**
     * @param lhss - the left-hand sides of the rewrite rules regarding which
     *  we check which symbols of terms are redexes
     */
    public ReduceRHSChecker(Iterable<Rule> rules) {

        this.defSymbolsToRules = new HashMap<FunctionSymbol, Pair<LinkedHashSet<Rule>, LinkedHashSet<Rule>>>();
        this.rule2overlap = new HashMap<Rule,Boolean>();
        Set<Rule> allRules = new LinkedHashSet<Rule>();

        for (Rule r : rules) {
            this.addRule(allRules, r);
        }
        this.allRules = ImmutableCreator.create(allRules);
        this.isEmpty = this.allRules.isEmpty();
    }

    private void addRule(Set<Rule> allRules, Rule r) {
        r = r.getStandardRepresentation();

        // do we have q already?
        if (allRules.contains(r)) {
            return;
        }

        // finally add q
        boolean linear = r.getLeft().isLinear();
        FunctionSymbol f = r.getRootSymbol();
        Pair<LinkedHashSet<Rule>, LinkedHashSet<Rule>> pair = this.defSymbolsToRules.get(f);
        if (pair == null) {
            pair = new Pair<LinkedHashSet<Rule>, LinkedHashSet<Rule>>(new LinkedHashSet<Rule>(), new LinkedHashSet<Rule>());
            this.defSymbolsToRules.put(f, pair);
        }

        if (linear) {
            pair.x.add(r);
        } else {
            pair.y.add(r);
        }
        allRules.add(r);
    }

    /**
     * checks whether t can be rewritten
     * @param t
     * @param fs
     */
    public void collectRewritablePositionsAndRules(Rule r, Map<Position,Set<Pair<Rule,TRSTerm>>> pos2rules) {
        if (!this.isEmpty) {
            this.collectRewritablePositionsAndRuleNotEmpty(r, pos2rules);
        }
    }

    private void collectRewritablePositionsAndRuleNotEmpty(Rule r, Map<Position,Set<Pair<Rule,TRSTerm>>> pos2rules) {
        if (Globals.useAssertions) {
            assert(!this.isEmpty);
        }
        TRSTerm t = r.getRight();

        for (Pair<Position, TRSTerm> pair : t.getPositionsWithSubTerms()) {
            if (pair.y.isVariable())
             {
                continue; // only non-var positions
            }
            TRSFunctionApplication subTerm = (TRSFunctionApplication) pair.y;
            Pair<? extends Set<Rule>, ? extends Set<Rule>> linearNonLinear = this.defSymbolsToRules.get(subTerm.getRootSymbol());
            if (linearNonLinear != null) {
                for (Rule linearRule : linearNonLinear.x) {
                    TRSFunctionApplication linear = linearRule.getLeft();
                    if (linear.linearMatches(subTerm)) {
                        Set<Pair<Rule,TRSTerm>> rules = pos2rules.get(pair.x);
                        if (rules == null) {
                            rules = new LinkedHashSet<Pair<Rule,TRSTerm>>();
                            pos2rules.put(pair.x, rules);
                        }
                        rules.add(new Pair<Rule,TRSTerm>(linearRule,r.getRight().replaceAt(pair.x, linearRule.getRight().applySubstitution(linear.getMatcher(subTerm)))));
                    }
                }
                for (Rule nonLinearRule : linearNonLinear.y) {
                    TRSFunctionApplication nonLinear = nonLinearRule.getLeft();
                    if (nonLinear.matches(subTerm)) {
                        Set<Pair<Rule,TRSTerm>> rules = pos2rules.get(pair.x);
                        if (rules == null) {
                            rules = new LinkedHashSet<Pair<Rule,TRSTerm>>();
                            pos2rules.put(pair.x, rules);
                        }
                        rules.add(new Pair<Rule,TRSTerm>(nonLinearRule,r.getRight().replaceAt(pair.x, nonLinearRule.getRight().applySubstitution(nonLinear.getMatcher(subTerm)))));
                    }
                }
            }
        }
    }

    public boolean doesNotOverlap(Rule rule) {
        TRSFunctionApplication left = rule.getLeft();
        Boolean overlap = this.rule2overlap.get(rule);
        if (overlap == null) {
            overlap = false;
outerLoop:  for (Rule otherRule : this.allRules) {
                if (rule.equals(otherRule)) {
                    continue;
                }
                for (TRSTerm subTerm : otherRule.getLeft().getNonVariableSubTerms()) {
                    if (left.unifiesVarDisjoint(subTerm)) {
                        overlap = true;
                        break outerLoop;
                    }
                }
            }
            if (!overlap) {
outerLoop2:
                for (Pair<Position,TRSFunctionApplication> pair : left.getNonRootNonVariablePositionsWithSubTerms()) {
                    TRSTerm subTerm = pair.y;
                    for (Rule otherRule : this.allRules) {
                        if (otherRule.getLeft().unifiesVarDisjoint(subTerm)) {
                            overlap = true;
                            break outerLoop2;
                        }
                    }
                }
            }
            this.rule2overlap.put(rule, overlap);
        }
        return !overlap;
    }

}
