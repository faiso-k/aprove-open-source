package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

public interface Labeller extends Exportable, XMLObligationExportable {

    public Map<FunctionSymbol, FunctionSymbol> getLabelToOriginMap();

    public void addLabeled(Rule rule,
        Collection<Rule> addHere,
        LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public void addQuasiLabeledPairs(Rule rule,
        Collection<Rule> addHere,
        Set<FunctionSymbol> headSyms,
        LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public void addLabeled(TRSFunctionApplication term,
        Set<TRSFunctionApplication> addHere,
        LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public Rule unlabel(Rule rule);

    //    public Term unlabel(Term term);
    public Set<Rule> getDecreasingRules(LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public Set<Rule> getDecreasingRules(Collection<FunctionSymbol> fs,
        LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public static class EffectiveChecker {

        /**
         * a labelling is ineffective iff
         * there is a mapping from syms to labelled syms such that
         * system.x[  f/labelF  ] subseteq system.y
         */
        public static boolean checkIneffective(final Iterable<Pair<Rule, Collection<Rule>>> system,
            final Labeller l,
            final SATCheckerFactory factory,
            final Abortion aborter) throws AbortionException {
            final Map<FunctionSymbol, Variable<None>> labeledToVar = new HashMap<FunctionSymbol, Variable<None>>();
            final Map<FunctionSymbol, FunctionSymbol> labeledToOrigin = l.getLabelToOriginMap();
            final FormulaFactory<None> ff = new FullSharingFactory<None>();

            final Map<FunctionSymbol, FunctionSymbol> tmpOriginToLabeled =
                new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

            Formula<None> res = ff.buildConstant(true);

            // express for every original rule that there must be some
            // labelled rule with only chosen labelled function-symbols
            for (final Pair<Rule, Collection<Rule>> rules : system) {
                Formula<None> originRuleFormula = null;
                labelRule: for (final Rule labelRule : rules.y) {
                    tmpOriginToLabeled.clear();
                    for (final FunctionSymbol labelF : labelRule.getFunctionSymbols()) {
                        final FunctionSymbol f = labeledToOrigin.get(labelF);
                        final FunctionSymbol currLab = tmpOriginToLabeled.put(f, labelF);
                        if (currLab != null && !currLab.equals(labelF)) {
                            // we have a conflict in this labelRule, as we have
                            // two different labelled symbols with same origin.
                            // hence, this rule cannot be the chosen rule.
                            continue labelRule;
                        }
                    }
                    Formula<None> ruleFormula = ff.buildConstant(true);
                    // okay, no conflict in this rule, so add formula
                    for (final FunctionSymbol labelF : tmpOriginToLabeled.values()) {
                        Variable<None> v = labeledToVar.get(labelF);
                        if (v == null) {
                            v = ff.buildVariable();
                            labeledToVar.put(labelF, v);
                        }
                        ruleFormula = ff.buildAnd(ruleFormula, v);
                    }
                    // so we have the formula for one labelled rule, let us
                    // combine it with the originRuleFormula
                    if (originRuleFormula == null) {
                        originRuleFormula = ruleFormula;
                    } else {
                        originRuleFormula = ff.buildOr(originRuleFormula, ruleFormula);
                    }
                }

                // now let us combine the originRuleFormula with the result formula
                if (originRuleFormula == null) {
                    // for this original rule there is no corresponding original,
                    // hence we are not ineffective.
                    return false;
                } else {
                    res = ff.buildAnd(res, originRuleFormula);
                }
            }

            // so we have our formula for the rules. Now we must ensure that
            // that for each of the labelled version of f, exactly one is chosen.
            final Map<FunctionSymbol, List<Variable<None>>> originToVariables =
                new HashMap<FunctionSymbol, List<Variable<None>>>();
            for (final Map.Entry<FunctionSymbol, Variable<None>> labelToVar : labeledToVar.entrySet()) {
                final FunctionSymbol originF = labeledToOrigin.get(labelToVar.getKey());
                final Variable<None> v = labelToVar.getValue();
                List<Variable<None>> vars = originToVariables.get(originF);
                if (vars == null) {
                    vars = new ArrayList<Variable<None>>();
                    originToVariables.put(originF, vars);
                }
                vars.add(v);
            }

            Variable<None>[] varArray = new Variable[20];
            for (final List<Variable<None>> vars : originToVariables.values()) {
                Formula<None> atMostOneVar = ff.buildConstant(true);
                varArray = vars.toArray(varArray);
                final int n = vars.size();
                for (int i = 0; i < n; i++) {
                    final Variable<None> var = varArray[i];
                    for (int j = i + 1; j < n; j++) {
                        atMostOneVar = ff.buildNot(ff.buildAnd(varArray[j], var));
                    }
                }
                res = ff.buildAnd(res, atMostOneVar);
            }

            // finally check the formula
            final SATChecker sc = factory.getSATChecker();
            /* TODO
             * Please check how to deal with a fail here.
             *
             * -- thetux
             */
            try {
                return sc.solve(res, aborter) != null;
            } catch (final SolverException e) {
                return false;
            }

        }

    }

    /**
     * For the given function symbol, return all possible labelled variants.
     * @param funcSym a function symbol
     * @param xmlLabelMap tell this map about the labelled version of funcSym
     * @return all labelled versions of the symbol
     */
    public Collection<FunctionSymbol> labelFS(FunctionSymbol funcSym,
        Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap);

    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final int carrierSize, final boolean quasi);

    /**
     * returns null, if toCPF is supported for the concrete Labelling, and
     * and an non-null error message otherwise
     */
    public String isCPFSupported();
}
