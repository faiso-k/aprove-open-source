package aprove.verification.dpframework.DPProblem.TheoremProver.RuleCandidateHeuristics;

import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Choose rules f(...) -> r such that
 * if (a) there is no mutually recursive function:
 *       then require that there is some f such that
 *       all f-rules with a constructor ground term as rhs are oriented strictly
 * else (b) f calls some other function g somewhere; then
 *     i) r is subterm of a rhs of another f-rule OR
 *    ii) r is a constructor term (here we do disjunction!)
 *
 * @author fuhs
 */
public class SmallerHeuristic implements RuleCandidateHeuristic {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.TheoremProver.RuleCandidateHeuristics.SmallerHeuristic");

    @Override
    public Set<Set<Rule>> selectCandidatesAsDNF(ImmutableSet<Rule> protoCandidates,
            TRSFunctionApplication dpRhs, Set<Rule> forbiddenCandidates) {
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(protoCandidates, IDPPredefinedMap.EMPTY_MAP);
        Set<FunctionSymbol> defSyms = analysis.getDefinedSymbols();

        Set<FunctionSymbol> mutuallyRecursiveSyms = SmallerHeuristic.computeMutuallyRecursiveSyms(protoCandidates, defSyms, analysis);

        Set<Set<Rule>> dnf = new LinkedHashSet<Set<Rule>>();
        Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = analysis.getRuleMap();

        int numberOfMRSs = mutuallyRecursiveSyms.size();
        if (numberOfMRSs == 0) {
            // all functions only call themselves;
            // demand that for one of them, /all/ rules with constructor RHSs are oriented strictly
            Set<Rule> conjuncts = new LinkedHashSet<Rule>();
            for (Entry<FunctionSymbol, ImmutableSet<Rule>> fToRules : ruleMap.entrySet()) {
                FunctionSymbol f = fToRules.getKey();
                Set<Rule> rules = fToRules.getValue();
                for (Rule rule : rules) {
                    if (! forbiddenCandidates.contains(rule)) {
                        Set<FunctionSymbol> fSyms = rule.getRight().getFunctionSymbols();
                        if (! fSyms.contains(f)) {
                            if (rule.getRight().getVariables().isEmpty()) {
                                conjuncts.add(rule);
                            }
                        }
                    }
                }
                if (! conjuncts.isEmpty()) {
                    dnf.add(conjuncts);
                }
            }
        }
        else {
            // (b): find f-rules where f is mutually recursive and ...
            //      * rhs is subterm of a rhs of another f-rule OR
            //      * there is no such f-rule, but one where the
            //        rhs is a constructor term
            for (FunctionSymbol f : mutuallyRecursiveSyms) {
                Set<Rule> fRules = ruleMap.get(f);
                for (Rule rule1 : fRules) {
                    if (! forbiddenCandidates.contains(rule1)) {
                        TRSTerm r1 = rule1.getRhsInStandardRepresentation();
                        // check for subterm of some other f-rule's rhs ...
                        for (Rule rule2 : fRules) {
                            TRSTerm r2 = rule2.getRhsInStandardRepresentation();
                            if (SUB.theSUB.inRelation(r2, r1)) {
                                Set<Rule> justRule1 = java.util.Collections.singleton(rule1);
                                dnf.add(justRule1);
                            }
                        }
                    }
                }
            }
            // ... and for constructor term
            if (dnf.isEmpty()) {
                for (FunctionSymbol f : mutuallyRecursiveSyms) {
                    Set<Rule> fRules = ruleMap.get(f);
                    for (Rule rule1 : fRules) {
                        if (! forbiddenCandidates.contains(rule1)) {
                            TRSTerm r1 = rule1.getRhsInStandardRepresentation();
                            boolean isConstructorTerm = this.isConstructorTerm(r1, defSyms);
                            if (isConstructorTerm) {
                                Set<Rule> justRule1 = java.util.Collections.singleton(rule1);
                                dnf.add(justRule1);
                            }
                        }
                    }
                }
            }
        }
        if (Globals.DEBUG_FUHS) {
            System.err.println(dnf);
        }
        if (dnf.isEmpty()) {
            SmallerHeuristic.log.log(Level.FINE,
                    "QDPTheoremProver: RuleHeuristic did not find strictness candidates, using most general candidates instead!");
            for (Rule rule : protoCandidates) {
                if (! forbiddenCandidates.contains(rule)) {
                    Set<Rule> justRule = java.util.Collections.singleton(rule);
                    dnf.add(justRule);
                }
            }
        }
        return dnf;
    }

    private boolean isConstructorTerm(TRSTerm t,
            Set<FunctionSymbol> defSyms) {
        Set<FunctionSymbol> syms = t.getFunctionSymbols();
        syms.retainAll(defSyms);
        return syms.isEmpty();
    }

    private static Set<FunctionSymbol> computeMutuallyRecursiveSyms(
            ImmutableSet<Rule> protoCandidates, Set<FunctionSymbol> defSyms,
            RuleAnalysis<Rule> analysis) {
        Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = analysis.getRuleMap();
        Set<FunctionSymbol> result = new LinkedHashSet<FunctionSymbol>();
        for (Entry<FunctionSymbol, ImmutableSet<Rule>> fToRules : ruleMap.entrySet()) {
            FunctionSymbol f = fToRules.getKey();
            Set<Rule> rules = fToRules.getValue();
            Set<TRSTerm> rhss = new LinkedHashSet<TRSTerm>(rules.size());
            for (Rule rule : rules) {
                rhss.add(rule.getRhsInStandardRepresentation());
            }
            Set<FunctionSymbol> rhsSyms = CollectionUtils.getFunctionSymbols(rhss);
            rhsSyms.remove(f);
            rhsSyms.retainAll(defSyms);
            if (! rhsSyms.isEmpty()) {
                result.add(f);
            }
        }
        return result;
    }
}
