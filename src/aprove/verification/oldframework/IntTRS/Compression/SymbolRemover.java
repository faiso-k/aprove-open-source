package aprove.verification.oldframework.IntTRS.Compression;

import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.stream.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Try to remove function symbol fs by combining all rules using it.
 */
class SymbolRemover {

    private class RenamingCentral {

        final String Separator = ":";
        int count = 0;

        Set<IGeneralizedRule> initiallyTransformToInternalFormat(Set<IGeneralizedRule> rules) {
            Set<IGeneralizedRule> result = new LinkedHashSet<>();
            Set<TRSVariable> variables = rules.stream().flatMap(x -> x.getAllVariables().stream()).collect(Collectors.toSet());
            Map<TRSVariable, TRSVariable> renamingMap = new LinkedHashMap<>();
            for (TRSVariable variable: variables) {
                TRSVariable newVariable = TRSTerm.createVariable(variable.getName() + Separator + count++);
                renamingMap.put(variable, newVariable);
            }
            for (IGeneralizedRule rule: rules) {
                result.add(rule.getWithRenamedVariables(renamingMap));
            }

            return result;
        }

        /**
         * Rename variables in input TRS term and return the resulting TRS term
         *
         * @param term TRS term with variables to be renamed
         * @return resulting TRS term after renaming
         */
        TRSTerm renameVariablesUniquely(TRSTerm term) {
            return term.renameVariables(getRenamingMap(term.getVariables()));
        }

        /**
         * Rename variables in input rewriting rule and return the resulting rewriting rule
         *
         * @param rule rewriting rule with variables to be renamed
         * @return resulting rewriting rule after renaming
         */
        IGeneralizedRule renameVariablesUniquely(IGeneralizedRule rule) {
            return rule.getWithRenamedVariables(getRenamingMap(rule.getAllVariables()));
        }

        /**
         * <input TRS variable, renamed TRS variable>
         *
         * @param variables
         * @return
         */
        Map<TRSVariable, TRSVariable> getRenamingMap(Set<TRSVariable> variables) {
            Map<TRSVariable, TRSVariable> renamingMap = new LinkedHashMap<>();
            for (TRSVariable variable : variables) {
                TRSVariable newVariable = TRSTerm.createVariable(getBaseName(variable.getName()) + Separator + count++);
                renamingMap.put(variable, newVariable);
            }
            return renamingMap;
        }

        String getBaseName(String x) {
            return x.substring(0, x.lastIndexOf(Separator));
        }

        IGeneralizedRule minimizeCounters(IGeneralizedRule rule) {
            Set<TRSVariable> variables = rule.getAllVariables();
            Map<TRSVariable, TRSVariable> renamingMap = new LinkedHashMap<>();
            Map<String, Integer> baseNameCounter = new DefaultValueMap<>(0);
            for (TRSVariable variable: variables) {
                String baseName = getBaseName(variable.getName());
                int counter = baseNameCounter.get(baseName);
                baseNameCounter.put(baseName, counter + 1);
                String newName = baseName + Separator + counter;
                TRSVariable newVariable = TRSTerm.createVariable(newName);
                renamingMap.put(variable, newVariable);
                inferVariableRenaming(newVariable);
            }
            return rule.getWithRenamedVariables(renamingMap);
        }

        private void inferVariableRenaming(TRSVariable variable) {
            variableRenaming.put(TRSTerm.createVariable(getBaseName(variable.getName())), variable);
        }

    }

    private Set<IGeneralizedRule> rules;
    private RuleMaps ruleMaps;
    private Abortion aborter;
    // set of terms for which we know that unification is not possible, so we don't need to
    // check again.
    private Set<Pair<TRSTerm, TRSTerm>> nonUnifiableTerms = new LinkedHashSet<>();
    private RemoveFreeVarsFromCond freeVarFilter;
    private final RenamingCentral renamingCentral = new RenamingCentral();
    private final Map<TRSVariable, TRSVariable> variableRenaming = new HashMap<>();
    private Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap;

    SymbolRemover(Set<IGeneralizedRule> rules, IDPPredefinedMap predefinedMap, Abortion aborter, Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap) {
        this.rules = renamingCentral.initiallyTransformToInternalFormat(rules);
        this.aborter = aborter;
        this.ruleMaps = new RuleMaps(this.rules);
        this.freeVarFilter = new RemoveFreeVarsFromCond(predefinedMap, false);
        this.combinedRulesMap = combinedRulesMap;
    }
    
    SymbolRemover(Set<IGeneralizedRule> rules, IDPPredefinedMap predefinedMap, Abortion aborter) {
        this.rules = renamingCentral.initiallyTransformToInternalFormat(rules);
        this.aborter = aborter;
        this.ruleMaps = new RuleMaps(this.rules);
        this.freeVarFilter = new RemoveFreeVarsFromCond(predefinedMap, false);
        this.combinedRulesMap = new HashMap<>();
    }

    /**
     * @param fs Function symbol to remove
     * @param filterFreeVarsFromCond if true, free variables in the conditions are removed
     * @return true if removal of this symbol was possible
     */
    boolean tryToRemoveSymbol(FunctionSymbol fs, boolean filterFreeVarsFromCond) {

        final Collection<IGeneralizedRule> leftRules = new LinkedHashSet<>(ruleMaps.left(fs));
        final Collection<IGeneralizedRule> rightRules = new LinkedHashSet<>(ruleMaps.right(fs));

        /*
         * We create one rule for each element of leftRules \times rightRules.
         * If both are bigger than one, removing this symbol would only increase
         * the size of the TRS, so don't do it.
         */
        if (leftRules.size() > 1 && rightRules.size() > 1) {
            return false;
        }
        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();

        Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> local_combinedRulesMap = new HashMap<>();
        
        // Iterate over the cartesian product of all rules having the given symbol as right resp. left hand side
        for (final IGeneralizedRule l : leftRules) {
            aborter.checkAbortion();
            IGeneralizedRule left = renamingCentral.renameVariablesUniquely(l);

            //Search for the position of the subterm matching the symbol to remove:
            final TRSFunctionApplication leftRight = (TRSFunctionApplication) left.getRight();
            TRSTerm leftRightSubterm = null;
            Position leftRightPos = null;
            if (leftRight.getRootSymbol().equals(fs)) {
                leftRightPos = Position.create();
                leftRightSubterm = leftRight;
            } else {
                for (final Pair<Position, TRSTerm> p : leftRight.getPositionsWithSubTerms()) {
                    final TRSTerm t = p.y;
                    if (t instanceof TRSFunctionApplication && ((TRSFunctionApplication) t).getRootSymbol().equals(fs)) {
                        leftRightSubterm = t;
                        leftRightPos = p.x;
                        break;
                    }
                }
            }

            //Could not find symbol, even though rule was marked as relevant in our map
            assert (leftRightPos != null) : "Symbol map broken";

            for (final IGeneralizedRule r : rightRules) {
                /*
                 * We do not want to combine a rule with itself, it may lead to
                 * infinitely many loop iterations
                 */
                if (l.equals(r)) {
                    newRules.add(l);
                    continue;
                }

                /*
                 * Furthermore, if we have
                 *  f(...) -> g(...)
                 *  g(...) -> g(...)
                 * We do not want to combine the two rules.
                 */
                if (!r.getRight().isVariable()
                    && r.getLeft().getRootSymbol().equals(((TRSFunctionApplication) r.getRight()).getRootSymbol())) {
                    continue;
                }


                /*
                 * Rename and unify the left hand side of the right rule and
                 * the right hand side of the left rule
                 */
                final IGeneralizedRule right = renamingCentral.renameVariablesUniquely(r);
                final TRSFunctionApplication rightLeft = right.getLeft();

                if (left.getLeft().getRootSymbol().equals(rightLeft.getRootSymbol())) {
                    return false;
                }

                final Pair<TRSTerm, TRSTerm> termsToUnify = new Pair<>(leftRightSubterm.renumberVariables("left"), rightLeft.renumberVariables("right"));
                if (nonUnifiableTerms.contains(termsToUnify)) {
                    return false;
                }

                final Unification unification = new Unification(leftRightSubterm, rightLeft);
                final TRSSubstitution mgu = unification.getMgu();

                // If there is no mgu, then we cannot combine these rules
                if (mgu == null) {
                    nonUnifiableTerms.add(termsToUnify);
                    return false;
                }

                final TRSTerm unpackedRightRight = right.getRight();

                final TRSTerm instantiatedRightRight = unpackedRightRight.applySubstitution(mgu);
                final TRSTerm renamedInstantiatedRightRight = renamingCentral.renameVariablesUniquely(instantiatedRightRight);

                //If we can use the same rule to narrow over and over again: don't.
                for (final TRSTerm subterm : renamedInstantiatedRightRight.getSubTerms()) {
                    if (subterm.isVariable() || subterm == renamedInstantiatedRightRight) {
                        continue;
                    }
                    final Unification leftRightLeftUnif = new Unification(subterm, r.getLeft());
                    if (leftRightLeftUnif.getMgu() != null) {
                        return false;
                    }
                }

                final TRSFunctionApplication leftLeft = left.getLeft();
                //In our rules, conditions are either null or a FunctionApp:
                final TRSTerm leftCondTerm = left.getCondTerm();
                final TRSTerm rightCondTerm = right.getCondTerm();

                // Build a combined conditional term, then update the variables:
                TRSTerm combinedConstraint = IDPv2ToIDPv1Utilities.getConjunction(leftCondTerm, rightCondTerm);
                if (combinedConstraint != null) {
                    combinedConstraint = combinedConstraint.applySubstitution(mgu);
                }

                // Generate a new rule
                IGeneralizedRule newRule =
                    IGeneralizedRule.create(leftLeft.applySubstitution(mgu), leftRight
                        .applySubstitution(mgu)
                        .replaceAt(leftRightPos, instantiatedRightRight), combinedConstraint);

                if (filterFreeVarsFromCond) {
                    newRule = freeVarFilter.removeFreeVarsFromCond(newRule);
                }

                //The variable condition may only be violated if we had this before:
                assert (!filterFreeVarsFromCond
                    || newRule.getLeft().getVariables().containsAll(newRule.getRight().getVariables()) || !(left
                        .getLeft()
                        .getVariables()
                        .containsAll(left.getRight().getVariables()) && right
                        .getLeft()
                        .getVariables()
                        .containsAll(right.getRight().getVariables()))) : "Introduced new free variables! Combined these two, got the last one:\n"
                        + left
                        + "\n"
                        + right
                        + "\n"
                        + newRule;

                IGeneralizedRule renamed = renamingCentral.renameVariablesUniquely(newRule);
                newRules.add(renamed);
                local_combinedRulesMap.put(renamed, new Pair<>(l,r));
            }
        }

        final Set<IGeneralizedRule> oldRules = new LinkedHashSet<>(leftRules);
        oldRules.addAll(rightRules);

        if (newRules.size() == 0 || oldRules.containsAll(newRules)) {
            return false;
        }

        //If we didn't return until now, combining was successful. Update all data:
        rules.removeAll(oldRules);
        rules.addAll(newRules);
        
        // update map of combined rules
        this.combinedRulesMap.putAll(local_combinedRulesMap);

        // Unregister each rule l -> r \in leftRules from rightRulesMap(root(l))
        for (final IGeneralizedRule rule : leftRules) {
            ruleMaps.unregisterFromRight(rule.getLeft().getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    ruleMaps.unregisterFromLeft(fa.getRootSymbol(), rule);
                }
            }
        }

        /*
         * Unregister each rule l -> r \in rightRules from leftRulesMap(f) for
         * all defined symbols f in r:
         */
        for (final IGeneralizedRule rule : rightRules) {
            final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            ruleMaps.unregisterFromLeft(rhs.getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    //If this is a defined symbol, we should unregister it:
                    ruleMaps.unregisterFromLeft(fa.getRootSymbol(), rule);
                }
            }
        }

        ruleMaps.remove(fs);

        if (Globals.DEBUG_MARC) {
            ruleMaps.checkValidity(rules);
        }

        // Register the newly created rules
        ruleMaps.update(newRules);

        return true;
    }

    public Set<IGeneralizedRule> getResult() {
        return rules.stream().map(renamingCentral::minimizeCounters).collect(toSet());
    }

    /**
     * Get global renaming map in current SymbolRemover
     *
     * @return global renaming map in current SymbolRemover
     */
    public Map<TRSVariable, TRSVariable> getVariableMapping() {
        return variableRenaming;
    }

}
