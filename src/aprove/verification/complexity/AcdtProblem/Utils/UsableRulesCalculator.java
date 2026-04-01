package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;
import java.util.concurrent.*;

import aprove.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Improved estimated usable rules from Thiemann's diss, Def. 3.26.
 *
 * No Q, just innermost.
 *
 * FIXME: Do we want to use an caching calculator for ICap (or more caching in general)?
 */
public class UsableRulesCalculator {

    /**
     * All variables in this set must be prefixed with {@link IcapAlgorithm#PREFIX_NOTCAP}.
     */
    private final ImmutableRuleSet<Rule> rules;

    private final IcapAlgorithm icap;

    private final ConcurrentHashMap<Rule, Set<Rule>> ruleToUsable;

    private UsableRulesCalculator(ImmutableRuleSet<Rule> rules,
            IcapAlgorithm icap, ConcurrentHashMap<Rule, Set<Rule>> cache) {
        if (Globals.useAssertions) {
            assert(IcapAlgorithm.checkVarPrefix(rules, IcapAlgorithm.PREFIX_NOTCAP));
        }
        this.rules = rules;
        this.icap = icap;
        this.ruleToUsable = cache;
    }

    /**
     * The {@link IcapAlgorithm} must use the same set of rules!
     * All variables in this set must be prefixed with {@link IcapAlgorithm#PREFIX_NOTCAP}.
     */
    public static UsableRulesCalculator create(ImmutableRuleSet<Rule> rules,
            IcapAlgorithm icap) {
        return new UsableRulesCalculator(rules, icap, new ConcurrentHashMap<Rule, Set<Rule>>());
    }
    /**
     * Returns a copy with a separate usable rule cache.
     */
    public UsableRulesCalculator createCopy() {
        return new UsableRulesCalculator(this.rules, this.icap,
                new ConcurrentHashMap<Rule, Set<Rule>>(this.ruleToUsable));
    }

    public ImmutableRuleSet<Rule> getRules() {
        return this.rules;
    }

    /**
     * Estimates usable rules. No restrictions on the variables in r.
     */
    public Set<Rule> estimateUsableRules(Rule rule) {
        return this.estimateUsableRules(rule, new LinkedHashSet<Rule>());
    }

    /**
     * Estimates usable rules of rule. The history contains the rules already
     * visited in the computation. This is needed to avoid infinite recursion.
     *
     * The "case (x)" comments refer to the bullet points in Def 3.26 in
     * Thiemann's diss.
     */
    private Set<Rule> estimateUsableRules(Rule rule, Set<Rule> history) {
        Rule renRule = rule.getWithRenumberedVariables(IcapAlgorithm.PREFIX_CAP_INPUT);
        Set<Rule> usableRules = this.ruleToUsable.get(rule);
        if (usableRules != null) {
            return usableRules;
        }
        if (!rule.getRight().isVariable() && !history.contains(renRule)) {
            history.add(renRule);
            TRSTerm t = renRule.getRight();
            Set<TRSTerm> S = new LinkedHashSet<TRSTerm>(renRule.getLeft().getArguments());
            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            ImmutableList<TRSTerm> faArgs = fa.getArguments();
            FunctionSymbol faRoot = fa.getRootSymbol();
            usableRules = new LinkedHashSet<Rule>();
            /* case (i) */
            List<TRSTerm> cappedArgs = this.icap.capTerms(faArgs, S, true);
            TRSFunctionApplication cappedFa = TRSTerm.createFunctionApplication(faRoot, cappedArgs);
            ruleLoop : for (Rule r : this.rules.getSubsetByRootSymbol(faRoot)) {
                TRSSubstitution sigma = cappedFa.getMGU(r.getLeft());
                if (sigma == null) {
                    continue;
                }
                for (TRSTerm localT : IterableConcatenator.create(cappedArgs, S)) {
                    if (!this.rules.termIsNormal(localT.applySubstitution(sigma))) {
                        continue ruleLoop;
                    }
                }
                usableRules.add(r);
            }
            /* case (ii) */
            for (TRSTerm arg : faArgs) {
                Rule argRule = Rule.create(renRule.getLeft(), arg);
                usableRules.addAll(this.estimateUsableRules(argRule, history));
            }

            /* case (iii) */
            LinkedHashSet<Rule> additionalUsableRules = new LinkedHashSet<Rule>();
            for (Rule r : usableRules) {
                additionalUsableRules.addAll(this.estimateUsableRules(r, history));
            }
            usableRules.addAll(additionalUsableRules);
        } else {
            /* case (iv) */
            usableRules = Collections.emptySet();
        }

        this.ruleToUsable.put(renRule, usableRules);
        return usableRules;
    }

}
