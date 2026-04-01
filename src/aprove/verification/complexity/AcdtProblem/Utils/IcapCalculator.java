package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;
import java.util.concurrent.*;

import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Convenient and caching wrapper for some use cases of ICapAlgorithm.
 */
public class IcapCalculator {

    private final static TRSVariable FRESHVAR = TRSVariable.createVariable(IcapAlgorithm.PREFIX_CAP_FRESH);

    /**
     * All variables in this set must be prefixed with {@link IcapAlgorithm#PREFIX_NOTCAP}.
     */
    private final ImmutableRuleSet<Rule> rules;

    /* Cached values below */

    /**
     * All variables in this set must be prefixed with {@link IcapAlgorithm#PREFIX_NOTCAP}.
     */
    private final ImmutableRuleSet<GeneralizedRule> invRules;

    /**
     * Maps a cdt to the list of capped RHSArgs.
     *
     * All variables in the value set are prefixed with
     * {@link IcapAlgorithm#PREFIX_CAP_FRESH} or
     * {@link IcapAlgorithm#PREFIX_CAP_INPUT}.
     */
    private final ConcurrentHashMap<Acdt, List<TRSTerm>> capCache;

    /**
     * Keys are (precedingCdt, toBeCappedCdt). Computes the
     * the capped LHS of toBeCappedCdt with regard to the reversed usable
     * rules of precedingCdt (i.e. it caches the capped terms needed
     * for forward instantiation, compare also Thiemann's diss, Theorem 5.5).
     *
     * FIXME: We want to consider each RHSArg of precedingCdt by itself.
     *
     * All variables in the value set are prefixed with
     * {@link IcapAlgorithm#PREFIX_CAP_FRESH} or
     * {@link IcapAlgorithm#PREFIX_CAP_INPUT}.
     */
    private final ConcurrentHashMap<CacheKey, TRSTerm> invCapCache;

    /**
     * {@link IcapAlgorithm} instance taking into account all rules.
     */
    private final IcapAlgorithm allRulesIcap;

    private final UsableRulesCalculator usableRulesCalc;

    /**
     * Cache. An element contained in this set has at least one collapsing usable rule.
     */
    private final Set<CacheKey> hasCollapsingUsableRule;

    public IcapCalculator(Set<Rule> rules) {
        this.capCache = new ConcurrentHashMap<Acdt, List<TRSTerm>>();
        this.invCapCache = new ConcurrentHashMap<CacheKey, TRSTerm>();
        ImmutableRuleSet<Rule> renumberedRules = new ImmutableRuleSet<Rule>(IcapAlgorithm.renumberedRules(rules));
        this.allRulesIcap = IcapAlgorithm.createUnsafe(renumberedRules);
        this.hasCollapsingUsableRule = Collection_Util.<CacheKey>createConcurrentHashSet();
        this.usableRulesCalc = UsableRulesCalculator.create(renumberedRules, this.allRulesIcap);
        this.rules = renumberedRules;
        this.invRules = this.reverseRules(renumberedRules);
    }

    public IcapCalculator(IcapCalculator oldCalc) {
        this.capCache = new ConcurrentHashMap<Acdt, List<TRSTerm>>(oldCalc.capCache);
        this.invCapCache = new ConcurrentHashMap<CacheKey, TRSTerm>(oldCalc.invCapCache);
        this.allRulesIcap = oldCalc.allRulesIcap;
        this.hasCollapsingUsableRule = Collection_Util.<CacheKey>createConcurrentHashSet(oldCalc.hasCollapsingUsableRule);
        this.usableRulesCalc = oldCalc.usableRulesCalc.createCopy();
        this.rules = oldCalc.rules;
        this.invRules = oldCalc.invRules;
    }

    /**
     * Makes a Cdt variable disjoint to any possible result of getCappedLhs
     * or getCappedRhs.
     */
    public Acdt renameVarDisjoint(Acdt cdt) {
        Set<TRSVariable> vars = cdt.getRule().getVariables();
        Map<TRSVariable,TRSVariable> freshVarMap = new LinkedHashMap<TRSVariable, TRSVariable>();
        int i=0;
        for (TRSVariable var : vars) {
            freshVarMap.put(var, TRSTerm.createVariable(IcapAlgorithm.PREFIX_NOTCAP + (i++)));
        }
        ImmutableMap<TRSVariable, TRSVariable> ifvm = ImmutableCreator.create(freshVarMap);
        return cdt.applySubstitution(TRSSubstitution.create(ifvm));
    }

    public TRSTerm getCappedLhs(TRSFunctionApplication precedingCdtLhs, TRSTerm precedingCdtRhsArg, Acdt toBeCapped) {
        CacheKey cacheKey =
            new CacheKey(precedingCdtLhs, precedingCdtRhsArg, toBeCapped.getRuleLHS());
        /* Already cached? */
        TRSTerm cappedLhs = this.invCapCache.get(cacheKey);
        if (cappedLhs != null) {
            return cappedLhs;
        }

        /* Do we already now that the usable rules are collapsing? */
        if (this.hasCollapsingUsableRule.contains(cacheKey)) {
            return IcapCalculator.FRESHVAR;
        }

        /* Else, we recompute the usable rules */
        Set<Rule> usableRules =
            this.usableRulesCalc.estimateUsableRules(Rule.create(precedingCdtLhs, precedingCdtRhsArg));
        ImmutableRuleSet<GeneralizedRule> reversedUR = this.reverseRules(usableRules);
        if (reversedUR == null) {
            this.hasCollapsingUsableRule.add(cacheKey);
            return IcapCalculator.FRESHVAR;
        }
        IcapAlgorithm reverseIcap = IcapAlgorithm.createUnsafe(reversedUR);

        TRSFunctionApplication renToBeCappedLhs =
            (TRSFunctionApplication)toBeCapped.getRuleLHS().renumberVariables(IcapAlgorithm.PREFIX_CAP_INPUT);
        cappedLhs = reverseIcap.capTerm(renToBeCappedLhs, Collections.<TRSTerm>emptySet(), false);
        this.invCapCache.put(cacheKey, cappedLhs);
        return cappedLhs;
    }

    public List<TRSTerm> getCappedRhs(Acdt cdt) {
        List<TRSTerm> cappedRhss = this.capCache.get(cdt);
        if (cappedRhss != null) {
            return cappedRhss;
        }
        TRSTerm t = this.allRulesIcap.capRuleRhs(cdt.getRule(), true);
        if (t.isVariable()) {
            throw new RuntimeException("Capping the cdt" + cdt +
                    " resulted in the rhs being a variable. But compound symbols are expected to be constructors!");
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        cappedRhss = fa.getArguments();
        this.capCache.put(cdt, cappedRhss);
        return cappedRhss;
    }

    public ImmutableRuleSet<Rule> getRules() {
        return this.rules;
    }

    public UsableRulesCalculator getURCalc() {
        return this.usableRulesCalc;
    }

    private ImmutableRuleSet<GeneralizedRule> reverseRules(Set<Rule> renumberedRules) {
        Set<GeneralizedRule> result = new LinkedHashSet<GeneralizedRule>();
        for (Rule rule : renumberedRules) {
            TRSTerm rhs = rule.getRight();
            if (rhs.isVariable()) {
                return null;
            }
            result.add(GeneralizedRule.create((TRSFunctionApplication)rhs, rule.getLeft()));
        }
        return new ImmutableRuleSet<GeneralizedRule>(result);
    }

    /**
     * Key for caches for reverse icap.
     */
    private static class CacheKey {
        public final TRSTerm precedingNodeLhs;
        public final TRSTerm precedingNodeRhs;
        public final TRSTerm lhsToBeCapped;
        private final int hashcode;

        public CacheKey(TRSTerm precedingNodeLhs, TRSTerm precedingNodeRhs, TRSTerm lhsToBeCapped) {
            this.precedingNodeLhs = precedingNodeLhs;
            this.precedingNodeRhs = precedingNodeRhs;
            this.lhsToBeCapped = lhsToBeCapped;
            this.hashcode = this.computeHashCode();
        }

        @Override
        public int hashCode() {
            return this.hashcode;
        }

        private int computeHashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((this.lhsToBeCapped == null) ? 0 : this.lhsToBeCapped.hashCode());
            result = prime
                    * result
                    + ((this.precedingNodeLhs == null) ? 0 : this.precedingNodeLhs
                            .hashCode());
            result = prime
                    * result
                    + ((this.precedingNodeRhs == null) ? 0 : this.precedingNodeRhs
                            .hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            CacheKey other = (CacheKey) obj;
            if (this.lhsToBeCapped == null) {
                if (other.lhsToBeCapped != null) {
                    return false;
                }
            } else if (!this.lhsToBeCapped.equals(other.lhsToBeCapped)) {
                return false;
            }
            if (this.precedingNodeLhs == null) {
                if (other.precedingNodeLhs != null) {
                    return false;
                }
            } else if (!this.precedingNodeLhs.equals(other.precedingNodeLhs)) {
                return false;
            }
            if (this.precedingNodeRhs == null) {
                if (other.precedingNodeRhs != null) {
                    return false;
                }
            } else if (!this.precedingNodeRhs.equals(other.precedingNodeRhs)) {
                return false;
            }
            return true;
        }

    }
}