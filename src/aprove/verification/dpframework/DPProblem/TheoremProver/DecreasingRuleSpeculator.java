package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPTheoremProverProcessor.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.RuleCandidateHeuristics.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * In this class we speculate a rule which most suitable as candidate for a
 * strict decreasing rule. Class can be extended by further heuristics
 *
 * @author micpar
 */
public class DecreasingRuleSpeculator {

    // gives us the DNF that states which rules to orient strictly
    private RuleHeuristic ruleHeuristic;

    public DecreasingRuleSpeculator(RuleHeuristic ruleHeuristic) {
        this.ruleHeuristic = ruleHeuristic;
    }

    public Triple<ImmutableSet<Rule>,MonotonicityConstraints,PartiallyMonotonicOrder> calculateDecreasingRulesWithPOLO(
            ImmutableSet<Rule> usableRules, TRSFunctionApplication dpRhs, SolverFactory solverFactory, ImmutableSet<Rule> P, Abortion aborter,
            Logger log, ImmutableSet<Integer> requiredMonotonicArgs, ImmutableSet<Rule> failedRules, ImmutableSet<Rule> candidates)
            throws AbortionException {

        // Monotonicity constraints for all function symbols
        Map<FunctionSymbol, MonotonicityConstraints> monCons = new LinkedHashMap<FunctionSymbol, MonotonicityConstraints>();
        MonotonicityCalculator monotonicityCalculator = new MonotonicityCalculator();
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(candidates, IDPPredefinedMap.EMPTY_MAP);
        for (FunctionSymbol funSym : analysis.getDefinedSymbols()) {
            // Add additional monotonicity constraint for DP-Rhs
            MonotonicityConstraints monCon = monotonicityCalculator.calculateRequirements(funSym, candidates, dpRhs);

            Map<FunctionSymbol, ImmutableSet<Integer>> constraints = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>(monCon
                    .getConstraints());
            Set<Integer> args = null;
            if (constraints.get(dpRhs.getRootSymbol()) != null) {
                args = new LinkedHashSet<Integer>(constraints.get(dpRhs.getRootSymbol()));
            }
            else {
                args = new LinkedHashSet<Integer>();
            }

            args.addAll(requiredMonotonicArgs);
            constraints.put(dpRhs.getRootSymbol(), ImmutableCreator.create(args));
            monCon = MonotonicityConstraints.create(ImmutableCreator.create(constraints));
            monCons.put(funSym, monCon);
        }

        // Feed constraint solver with full P, usable rules suffice, because we
        // can always apply the usable rules processor before this processor
        // monotonicity constraints
        OrderCalculator orderCalculator = solverFactory.getOrderCalculator();
        Set<Rule> orientThemWeakly = new LinkedHashSet<Rule>();
        orientThemWeakly.addAll(P);
        orientThemWeakly.addAll(usableRules);

        Set<Set<Rule>> strictnessCandidatesDNF;
        Triple<ImmutableSet<Rule>,MonotonicityConstraints,PartiallyMonotonicOrder> resultOrder = null;
        aborter.checkAbortion();

        switch (this.ruleHeuristic) {
        case ANY_RULE: {
            // docu-guess (fuhs): legacy code:
            // just demand that an arbitrary single rule is deleted unless
            // an earlier attempt using that rule has failed
            strictnessCandidatesDNF = new LinkedHashSet<Set<Rule>>();
            for (FunctionSymbol defsym : analysis.getDefinedSymbols()) {
                strictnessCandidatesDNF.add(new LinkedHashSet<Rule>(analysis.getRuleMap().get(defsym)));
            }
            Set<Set<Rule>> tmp = new LinkedHashSet<Set<Rule>>();
            Iterator<Set<Rule>> setIter = strictnessCandidatesDNF.iterator();
            while (setIter.hasNext()) {
                Set<Rule> rules = setIter.next();
                Iterator<Rule> ruleIter = rules.iterator();
                while (ruleIter.hasNext()) {
                    Set<Rule> innertmp = new LinkedHashSet<Rule>();
                    Rule rule = ruleIter.next();
                    innertmp.add(rule);
                    if (failedRules == null) {
                        tmp.add(innertmp);
                    }
                    else {
                        if (!failedRules.contains(rule)) {
                            tmp.add(innertmp);
                        }
                    }
                }
            }
            strictnessCandidatesDNF = tmp;
            break;
        }
        default:
            RuleCandidateHeuristic h = this.getRuleCandidateHeuristic();
            Set<Rule> forbiddenRules = failedRules == null ? java.util.Collections.<Rule>emptySet() : failedRules;
            strictnessCandidatesDNF = h.selectCandidatesAsDNF(candidates, dpRhs, forbiddenRules);
        }
        log.log(Level.FINE, "These are the strictness candidates: " + strictnessCandidatesDNF);

        // If there are no strictness candidates, we give up.
        if (strictnessCandidatesDNF.isEmpty()) {
            return null;
        }

        resultOrder = orderCalculator.calculateStrictRulesAndMonotonicity(orientThemWeakly, candidates, strictnessCandidatesDNF, monCons,
                aborter);

        return resultOrder;
    }

    private RuleCandidateHeuristic getRuleCandidateHeuristic() {
        switch (this.ruleHeuristic) {
        case SMALL_OR_LAST_CALL: return new SmallerHeuristic();
        case ANY_RULE:
        default:
            throw new RuntimeException("No known implementation for " +
                    this.ruleHeuristic + " yet!");
        }
    }
}
