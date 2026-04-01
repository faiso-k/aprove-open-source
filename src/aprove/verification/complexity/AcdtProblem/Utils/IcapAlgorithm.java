package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;

import aprove.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * ICap from Thiemann's thesis (Def 3.11) (without Q, only innermost/full).
 */
public class IcapAlgorithm {

    /*
     * The constants below are used to get variable disjoint terms for unification.
     */

    /**
     * Terms to be capped may only use variables starting with this string.
     */
    public final static String PREFIX_CAP_INPUT = "x";

    /**
     * Fresh variables generated during cap-calculation are prefixed
     * with this string.
     */
    public final static String PREFIX_CAP_FRESH = "y";

    /**
     * This prefix is used variables in terms which must be variable disjoint
     * to both input to a cap function as well as any capped term.
     *
     * Internally, this prefix is used for the rule set. Externally, it may
     * be useful for unifying with a capped term.
     */
    public final static String PREFIX_NOTCAP = "z";

    /**
     * All variables in this set must be prefixed with {@link #PREFIX_NOTCAP}.
     */
    private final ImmutableRuleSet<? extends GeneralizedRule> rules;

    /**
     * All variables in the set <code>rules<</code> must be prefixed with
     * {@link #PREFIX_NOTCAP}.
     */
    private IcapAlgorithm(ImmutableRuleSet<? extends GeneralizedRule> rules) {
        this.rules = rules;
    }

    /**
     * All variables in the set <code>rules<</code> must be prefixed with
     * {@link #PREFIX_NOTCAP}.
     *
     * @see IcapAlgorithm#rules
     */
    public static IcapAlgorithm createUnsafe(ImmutableRuleSet<? extends GeneralizedRule> rules) {
        return new IcapAlgorithm(rules);
    }

    /**
     * @see IcapAlgorithm#createUnsafe(ImmutableRuleSet)
'     */
    public static IcapAlgorithm createUnsafe(Set<? extends GeneralizedRule> rules) {
        return new IcapAlgorithm(new ImmutableRuleSet<GeneralizedRule>(rules));
    }

    public static IcapAlgorithm create(Set<? extends GeneralizedRule> rules) {
        ImmutableRuleSet<GeneralizedRule> renRules =
            new ImmutableRuleSet<GeneralizedRule>(IcapAlgorithm.renumberedGRules(rules));
        return new IcapAlgorithm(renRules);
    }

    /**
     * Makes a Rule variable disjoint to any possible result of getCappedLhs
     * or getCappedRhs.
     */
    public Rule renameVarDisjoint(Rule r) {
        Set<TRSVariable> vars = r.getVariables();
        Map<TRSVariable,TRSVariable> freshVarMap = new LinkedHashMap<TRSVariable, TRSVariable>();
        int i=0;
        for (TRSVariable var : vars) {
            freshVarMap.put(var, TRSTerm.createVariable(IcapAlgorithm.PREFIX_NOTCAP + (i++)));
        }
        ImmutableMap<TRSVariable, TRSVariable> ifvm = ImmutableCreator.create(freshVarMap);
        return r.applySubstitution(TRSSubstitution.create(ifvm));
    }

    /**
     * Computes the ICap of the RHS of the rule, with S being the LHS.
     * There are no restrictions for the variables in r.
     */
    public TRSTerm capRuleRhs(GeneralizedRule r, boolean innermost) {
        GeneralizedRule renRule = r.getWithRenumberedVariables(IcapAlgorithm.PREFIX_CAP_INPUT);
        return this.capTerm(renRule.getRight(), Collections.<TRSTerm>singleton(renRule.getLeft()), innermost);
    }

    /**
     * In t, S all variable names must start with {@link #PREFIX_CAP_INPUT}.
     */
    public TRSTerm capTerm(TRSTerm t, Set<TRSTerm> S, boolean innermost) {
        if (Globals.useAssertions) {
            assert(IcapAlgorithm.checkVarPrefix(Collections.singleton(t), IcapAlgorithm.PREFIX_CAP_INPUT));
            assert(IcapAlgorithm.checkVarPrefix(S, IcapAlgorithm.PREFIX_CAP_INPUT));
        }
        IcapState st = new IcapState(S, this.rules);
        return this.icap(t, innermost, st);
    }

    /**
     * In ts, S all variable names must start with {@link #PREFIX_CAP_INPUT}.
     */
    public List<TRSTerm> capTerms(List<? extends TRSTerm> ts, Set<TRSTerm> S, boolean innermost) {
        if (Globals.useAssertions) {
            for (TRSTerm t : ts) {
                assert(IcapAlgorithm.checkVarPrefix(Collections.singleton(t), IcapAlgorithm.PREFIX_CAP_INPUT));
            }
            assert(IcapAlgorithm.checkVarPrefix(S, IcapAlgorithm.PREFIX_CAP_INPUT));
        }
        IcapState st = new IcapState(S, this.rules);
        ArrayList<TRSTerm> capTs = new ArrayList<>(ts.size());
        for (TRSTerm t : ts) {
            capTs.add(this.icap(t, innermost, st));
        }
        return capTs;
    }

    /**
     * ICap from Thiemann's thesis (Def 3.11). Use only innermost/not innermost
     * instead of Q.
     *
     * All variable names in rules must start with {@link #PREFIX_NOTCAP}
     * All variable names in t must start with {@link #PREFIX_CAP_INPUT}
     * All variable names in the result start with {@link #PREFIX_CAP_INPUT}
     * {@link #PREFIX_CAP_FRESH}.
     */
    private TRSTerm icap(TRSTerm t, boolean innermost, IcapState st) {
        if (t.isVariable()) {
            if (innermost && st.isSubtermOfS(t)) {
                return t;
            } else {
                return st.getFreshVar();
            }
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            ImmutableList<TRSTerm> args = fa.getArguments();
            ArrayList<TRSTerm> cappedArgs = new ArrayList<TRSTerm>(args.size());
            for (TRSTerm arg : args) {
                cappedArgs.add(this.icap(arg, innermost, st));
            }
            TRSFunctionApplication cappedTerm = TRSTerm.createFunctionApplication(fa.getRootSymbol(), cappedArgs);
            if (this.icapOk(cappedTerm, innermost, st)) {
                return cappedTerm;
            } else {
                return st.getFreshVar();
            }
        }
    }

    /**
     * Implements condition 2 of Def 3.11 in Thiemann's thesis.
     * @param innermost
     */
    private boolean icapOk(TRSFunctionApplication cappedTerm, boolean innermost, IcapState st) {
        outer : for (GeneralizedRule r : this.rules.getSubsetByRootSymbol(cappedTerm.getRootSymbol())) {
            TRSFunctionApplication lhs = r.getLeft();
            TRSSubstitution mgu = cappedTerm.getMGU(lhs);
            if (mgu == null) {
                continue;
            }
            if (innermost) {
                for (TRSTerm t : IterableConcatenator.create(lhs.getArguments(), st.S)) {
                    if (!this.rules.termIsNormal(t.applySubstitution(mgu))) {
                        continue outer;
                    }
                }
            }
            return false;
        }
        return true;
    }

    /**
     * Returns a set where all rules where renumbered with {@link #PREFIX_NOTCAP}.
     */
    public static Set<GeneralizedRule> renumberedGRules(Set<? extends GeneralizedRule> rawRules) {
        Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>();
        for (GeneralizedRule rawRule : rawRules) {
            rules.add(rawRule.getWithRenumberedVariables(IcapAlgorithm.PREFIX_NOTCAP));
        }
        return rules;
    }

    /**
     * Returns a set where all rules where renumbered with {@link #PREFIX_NOTCAP}.
     */
    public static Set<Rule> renumberedRules(Set<Rule> rawRules) {
        Set<Rule> rules = new LinkedHashSet<Rule>();
        for (Rule rawRule : rawRules) {
            rules.add(rawRule.getWithRenumberedVariables(IcapAlgorithm.PREFIX_NOTCAP));
        }
        return rules;
    }

    public static boolean checkVarPrefix(Collection<? extends HasVariables> rules, String prefix) {
        @SuppressWarnings("unchecked")
        Set<TRSVariable> vars = (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(rules);
        for (TRSVariable var : vars) {
            if (!var.getName().startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }


    private static class IcapState {
        final Set<TRSTerm> S;
        private int freshCnt;

        IcapState(Set<TRSTerm> S, RuleSet<? extends GeneralizedRule> rules) {
            this.S = S;
        }

        public boolean isSubtermOfS(TRSTerm t) {
            for (TRSTerm s : this.S) {
                if (s.hasSubterm(t)) {
                    return true;
                }
            }
            return false;
        }

        TRSVariable getFreshVar() {
            return TRSTerm.createVariable(IcapAlgorithm.PREFIX_CAP_FRESH + this.freshCnt++);
        }
    }

}