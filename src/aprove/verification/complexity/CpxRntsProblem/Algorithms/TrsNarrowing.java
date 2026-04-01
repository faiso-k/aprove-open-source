package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.TreeSet;

import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Applies narrowing to inner basic terms of the right-hand side of of a rule.
 *
 * @author mnaaf
 */
public class TrsNarrowing {

    //avoid explosion of the TRS: limit number of new rules to replace a single rule
    private static final int LIMIT_PER_RULE = 20;

    /**
     * Narrow a given set of rules by using a (possibly different) set of rules.
     *
     * @param toNarrow The rules that should be narrowed (i.e. the rhs will be replaced)
     * @param allRules The rules that can be used to narrow basic terms
     * @param defSym The set of defined symbols of the TRS (to distinguish functions/ctors)
     *
     * @return A new set of rules that replaces rules from `toNarrow` by narrowed version.
     * Note that the result can be much larger, if many rules can be used for narrowing.
     * If a rule in `toNarrow` cannot be narrowed, or if the narrowing would introduce
     * too many new rules (see LIMIT_PER_RULE), the rule is kept without changes in the result.
     */
    public static Set<WeightedRule> narrowRules(Set<WeightedRule> toNarrow, Set<WeightedRule> allRules, Set<FunctionSymbol> defSym) {
        //determine names that must not be used for fresh variables
        Set<TRSVariable> usedNames = new LinkedHashSet<>();
        for (WeightedRule r: toNarrow) {
            for (TRSVariable x: r.getTRSVariables()) {
                usedNames.add(x);
            }
        }
        //narrow each rule in `toNarrow` one by one
        Set<WeightedRule> res = new LinkedHashSet<>();
        for (WeightedRule todo : toNarrow) {

            //compute positions of inner basic terms suitable for narrowing
            Set<Position> positions = new TreeSet<>(new InnerMostPositionComparator());
            TRSTerm right = todo.getRight();
            positions.addAll(right.getPositions());
            Set<Position> narrowPositions = new LinkedHashSet<>();
            OUTER: for (Position pi : positions) {
                //check that this subterm is a defined-function application
                TRSTerm t = right.getSubterm(pi);
                if (t.isVariable()) {
                    continue OUTER;
                }
                FunctionSymbol subroot = ((TRSFunctionApplication)t).getRootSymbol();
                if (!defSym.contains(subroot)) {
                    continue OUTER;
                }
                //only perform innermost narrowing (check whether we can narrow below pi)
                for (Position tau : narrowPositions) {
                    if (pi.isPrefixOf(tau)) {
                        continue OUTER;
                    }
                }
                //ensure that we only narrow funapps that are inside an outer function
                //e.g. in f(x) -> f(g(x)) we can narrow g, but in f(x) -> g(x) we can't.
                boolean ok = false;
                for (Position prefix : pi.getTruePrefixes()) {
                    TRSFunctionApplication funapp = (TRSFunctionApplication)right.getSubterm(prefix);
                    if (defSym.contains(funapp.getRootSymbol())) {
                        ok = true;
                        break;
                    }
                }
                if (ok) {
                    narrowPositions.add(pi);
                }
            }

            //for every inner basic term, apply all possible rules to obtain several new rhss
            //if there are several narrowing positions, the following narrowing steps have
            //to be applied to all previously created rules, which are stored in `todoRules`.
            Set<WeightedRule> todoRules = new LinkedHashSet<>();
            todoRules.add(todo);
            for (Position pi : narrowPositions) {
                //set of new rules that are created in this narrowing step
                Set<WeightedRule> newRules = new LinkedHashSet<>();

                //narrow all previously created rules at position pi
                for (WeightedRule rule : todoRules) {
                    TRSTerm t = rule.getRight().getSubterm(pi);
                    assert(!t.isVariable());

                    //check if t can be narrowed via each rule r by using unification
                    for (WeightedRule r : allRules) {
                        Rule varRenamedRule = r.getRule().renameVariables(usedNames);
                        TRSSubstitution unifier = t.getMGU(varRenamedRule.getLeft());
                        if (unifier != null) {
                            TRSFunctionApplication lhs = rule.getLeft().applySubstitution(unifier);
                            TRSTerm rhs = rule.getRight().replaceAt(pi, varRenamedRule.getRight()).applySubstitution(unifier);
                            WeightedRule unified = WeightedRule.create(lhs, rhs, rule.getWeight()+r.getWeight());
                            newRules.add(unified);
                            usedNames.addAll(unified.getTRSVariables()); //might contain renamed variables (e.g. x')
                        }
                    }
                }

                //narrowing on the next position has to be applied to all rules created in this step
                todoRules = newRules;
            }

            //avoid rule explosion by some heuristic
            if (todoRules.size() > LIMIT_PER_RULE) {
                narrowPositions.clear();
                todoRules.clear();
            }

            //keep rules where narrowing was not possible or the heuristic stepped in
            if (narrowPositions.isEmpty()) {
                todoRules.add(todo);
            }

            res.addAll(todoRules);
        }
        return res;
    }

}
