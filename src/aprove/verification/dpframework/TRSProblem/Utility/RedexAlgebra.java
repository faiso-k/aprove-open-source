package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * this class represents a CoreRedexAlgebra \mathcal{A} = <A, [.], isRedex>.<br>
 * it can be reduced to core RedexAlgebra by calling {@link buildCore()}<br>
 * for more information see [ENDRULLIS_HENRIKS_2009]
 * @author Tim Enger
 */

public class RedexAlgebra {

    final TRSFunctionApplication bot;

    /**
     * non-empty set A
     */
    private Set<TRSFunctionApplication> A;

    /**
     * top and topResult is needed for extension to top-Algebra
     */
    private FunctionSymbol top = null;
    private TRSFunctionApplication topResult;

    /**
     * underlying set of rules
     */
    private ImmutableSet<? extends GeneralizedRule> rules;

    /**
     * underlying signature
     */
    private Set<FunctionSymbol> signature;

    public RedexAlgebra(ImmutableSet<? extends GeneralizedRule> rules, Set<FunctionSymbol> signature) {
        this.rules = rules;
        this.signature = signature;
        FreshNameGenerator gen = new FreshNameGenerator(signature, FreshNameGenerator.APPEND_NUMBERS);
        this.bot =
            TRSTerm.createFunctionApplication(
                FunctionSymbol.create(gen.getFreshName( "bot", false), 0),
                ImmutableCreator.create(new ArrayList<TRSFunctionApplication>())
            );
        this.A = this.createA(rules);
    }

    /**
     * [.] interpretation function
     * @param f {@link FunctionSymbol}
     * @param args arguments to interpret
     * @return interpretation [f](a_1,....,a_n) with a_i \in args
     */
    public TRSFunctionApplication interpret(FunctionSymbol f, List<TRSFunctionApplication> args) {
        if (f.equals(this.top)) {
            return this.topResult;
        }
        TRSFunctionApplication funapp =
            TRSTerm.createFunctionApplication(f, ImmutableCreator.create((ArrayList<TRSFunctionApplication>)args));
        return this.shrink(funapp);
    }

    /**
     * @param f
     * @return true, if f(args...) is an instance of a linear lhs of R
     */
    public boolean isRedex(FunctionSymbol f, List<TRSFunctionApplication> args) {
        TRSFunctionApplication funapp =
            TRSTerm.createFunctionApplication(f, ImmutableCreator.create((ArrayList<TRSFunctionApplication>) args));
        for (TRSTerm lhs : CollectionUtils.getLeftHandSides(this.rules)) {
            if (lhs.isLinear()) {
                if (lhs.matches(funapp)) {
                    // if (funapp.getMGU(lhs) != null) {
                    return true;
                }
            }
        }
        return false;
    }

    public void extendTop(FunctionSymbol top) {
        this.top = top;
        // arbitrary but fixed a \in A
        if (!this.A.isEmpty()) {
            this.topResult = this.A.iterator().next();
        }
    }

    @SuppressWarnings("unchecked")
    private Set<TRSFunctionApplication> createA(ImmutableSet<? extends GeneralizedRule> rules) {
        Set<TRSFunctionApplication> setA = new LinkedHashSet<TRSFunctionApplication>();
        setA.add(this.bot);
        /* t \in A for every proper subterm t of cut(l)
         * with l a linear lhs of R
         */
        Map<TRSTerm, TRSTerm> replaceMap = new LinkedHashMap<TRSTerm, TRSTerm>();
        for (TRSVariable var : (Set<TRSVariable>)CollectionUtils.getVariables(rules)) {
            replaceMap.put(var, this.bot);
        }
        for (GeneralizedRule rule : rules) {
            TRSFunctionApplication lhs = rule.getLeft();
            if (lhs.isLinear()) {
                // replace all variables by bot -> cut(l)
                lhs = (TRSFunctionApplication) lhs.replaceAll(replaceMap);
                // not the root symbol
                for (TRSTerm t : lhs.getArguments()) {
                    for (TRSTerm subterm : ((TRSFunctionApplication) t).getSubTerms()) {
                        setA.add((TRSFunctionApplication) subterm);
                    }
                }
            }
        }
        List<TRSFunctionApplication> listA = new ArrayList<TRSFunctionApplication>(setA);
        // close under merge(s,t) for all s,t \in A
        boolean changed = true;
        while (changed) {
            changed = false;
            List<TRSFunctionApplication> addA = new ArrayList<TRSFunctionApplication>();
            // all Combinations to merge
            for (int i = 0; i < listA.size(); i++) {
                for (int j = i; j < listA.size(); j++) {
                    TRSFunctionApplication merge = this.merge(listA.get(i), listA.get(j));
                    if (!setA.contains(merge)) {
                        addA.add(merge);
                        changed = true;
                    }
                }
            }
            listA.addAll(addA);
        }
        return new LinkedHashSet<TRSFunctionApplication>(listA);
    }

    /**
     * reduce this RedexAlgebra to CoreRedexAlgebra<br>
     * <A_c, [.]_c, isRedex_c> where<br>
     * <ul>
     * <li>A_c = smallest set such that [f](a_1,...,a_n) \in A_c whenever f \in
     * Sigma and a_1,...,a_n \in A_c</li>
     * <li>[.]_c and IsRedex_c are restrictions of [.] and isRedex to A_c</li>
     * </ul>
     */
    public void buildCore() {
        Set<TRSFunctionApplication> core =
            new LinkedHashSet<TRSFunctionApplication>();

        boolean changed = true;
        while (changed) {
            changed = false;

            // add all constants
            for (FunctionSymbol f : this.signature) {
                if (f.getArity() == 0) {
                    changed |=
                        core.add(this.interpret(f,
                            new ArrayList<TRSFunctionApplication>()));
                } else {
                    if (!core.isEmpty()) {
                        List<List<TRSFunctionApplication>> perms =
                            Combinations.createCombinations(
                                new ArrayList<TRSFunctionApplication>(core),
                                f.getArity());

                        for (List<TRSFunctionApplication> i : perms) {
                            changed |= core.add(this.interpret(f, i));
                        }
                    }
                }
            }
        }
        this.A = core;
    }

    /**
     * merge(bot,t) = t <br>
     * merge(t,bot) = t <br>
     * merge(f(s_1,...,s_n),f(t_1,...,t_n)) =
     * f(merge(s_1,t_2),...,merge(s_n,t_n))<br>
     * @param s
     * @param t
     * @return
     */
    private TRSFunctionApplication merge(final TRSFunctionApplication s,
        final TRSFunctionApplication t) {
        // merge(bot,t2) = t2
        if (s.equals(this.bot)) {
            return t;
        }

        // merge(t1,bot) = t1
        if (t.equals(this.bot)) {
            return s;
        }

        /* merge(f(s_1,...,s_n),f(t_1,...,t_n))
         * = f(merge(s_1,t_2),...,merge(s_n,t_n))
         */
        if (s.getRootSymbol().equals(t.getRootSymbol())) {
            ArrayList<TRSFunctionApplication> args =
                new ArrayList<TRSFunctionApplication>();
            ImmutableList<TRSTerm> argsS = s.getArguments();
            ImmutableList<TRSTerm> argsT = t.getArguments();
            for (int i = 0; i < argsS.size(); i++) {
                TRSFunctionApplication merge =
                    this.merge((TRSFunctionApplication)argsS.get(i), (TRSFunctionApplication)argsT.get(i));
                args.add(merge);
            }
            return TRSTerm.createFunctionApplication(t.getRootSymbol(), ImmutableCreator.create(args));
        }
        return this.bot;
    }

    /**
     * @param s Term
     * @param t Term
     * @return true, if s can be obtained from t by replacing subterms of t by
     * bot, otherwise false
     */
    private boolean match(TRSFunctionApplication s, TRSFunctionApplication t) {
        if (s.equals(this.bot)) {
            return true;
        } else {
            if (s.getRootSymbol().equals(t.getRootSymbol())) {
                for (Pair<Position, TRSFunctionApplication> subterm : s.getNonRootNonVariablePositionsWithSubTerms()) {
                    if (!this.match((TRSFunctionApplication) s.getSubterm(subterm.x),
                        (TRSFunctionApplication) t.getSubterm(subterm.x))) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        return true;
    }

    /**
     * @param s
     * @return largest (w.r.t. number of Symbols) {@link TRSTerm t}\in terms such
     * that match(t,s) is true
     */
    private TRSFunctionApplication shrink(final TRSFunctionApplication s) {
        int max = 0;
        TRSFunctionApplication largestTerm = this.bot;

        for (TRSFunctionApplication t : this.A) {
            if (this.match(t, s)) {
                int count = t.getFunctionSymbolCount().size();
                // whenever two terms t1,t2 match s:
                // merge(t1,t2) is larger and matches s
                if (max == count) {
                    largestTerm = this.merge(largestTerm, t);
                } else if (max < count) {
                    max = count;
                    largestTerm = t;
                }
            }
        }
        return largestTerm;
    }

    public Set<TRSFunctionApplication> getA() {
        return this.A;
    }
}