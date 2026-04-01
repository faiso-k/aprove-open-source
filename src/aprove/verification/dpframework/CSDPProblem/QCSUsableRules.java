package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class QCSUsableRules {

    private final QTermSet q;

    private final ImmutableSet<Rule> r;

    private final ImmutableMap<FunctionSymbol, Set<Rule>> symbolToRules;

    private final GeneralizedTRS genR;

    private final ReplacementMap mu;

    private final boolean innermost;

    /* TODO this should be setable in the strategy */
    private CapMuEstimation eCapMu = Globals.simpleCapMu ? new SimpleCapMu()
            : new ICapMu();

    /**
     *
     * @param mu
     * @param r
     *            must be in first standard prefix form
     * @param q
     */
    private QCSUsableRules(ReplacementMap mu, ImmutableSet<Rule> r, QTermSet q,
            boolean innermost) {
        if (Globals.useAssertions) {
            for (Rule l_to_r : r) {
                l_to_r.getLeft()
                        .equals(l_to_r.getLhsInStandardRepresentation());
            }
        }
        this.mu = mu;
        this.r = r;
        this.q = q;
        this.innermost = innermost;

        Map<FunctionSymbol, Set<Rule>> rules = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (Rule l_to_r : r) {
            FunctionSymbol f = l_to_r.getRootSymbol();
            Set<Rule> rules_of_f = rules.get(f);
            if (rules_of_f == null) {
                rules_of_f = new LinkedHashSet<Rule>();
                rules.put(f, rules_of_f);
            }
            rules_of_f.add(l_to_r);
        }
        this.symbolToRules = ImmutableCreator.create(rules);

        this.genR = GeneralizedTRS.create(r);
    }

    public static QCSUsableRules create(QCSDPProblem problem) {
        ReplacementMap mu = problem.getReplacementMap();
        ImmutableSet<Rule> r = problem.getR();
        QTermSet q = problem.getQ();
        boolean innermost = problem.isInnermost();
        return new QCSUsableRules(mu, r, q, innermost);
    }

    public final ImmutableSet<Rule> estimatedCSUsableRules(Set<Rule> p) {
        Set<Rule> usable = new LinkedHashSet<Rule>();

        // add usable rules of t to usable
        for (Rule dp : p) {
            Rule l_to_r = dp
                    .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            this.estimatedCSUsableRules(usable, l_to_r);
        }
        return ImmutableCreator.create(usable);
    }

    public final ImmutableSet<Rule> estimatedCSUsableRules(Rule s_to_t) {
        Set<Rule> usable = new LinkedHashSet<Rule>();
        this.estimatedCSUsableRules(usable, s_to_t
                .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX));
        return ImmutableCreator.create(usable);
    }

    /**
     * Computes the estimated context-sensitive usable rules of a term t.
     * ([E08], Def. ??)
     *
     * @param s
     *            in third standard prefix form
     * @param t
     *            in third standard prefix form
     *
     * @return
     */
    public final ImmutableSet<Rule> estimatedCSUsableRules(Set<TRSTerm> s, TRSTerm t) {
        if (Globals.useAssertions) {
            assert (t.equals(t.renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX)));
            for (TRSTerm u : s) {
                assert (u.equals(u
                        .renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX)));
            }
        }
        /*
         * all rules found usable are added directly this set. recurse in added
         * rules immediately, so it is possible to abort recursion by checking
         * the existence of the current rule in this set.
         */
        Set<Rule> usable = new LinkedHashSet<Rule>();

        // add usable rules of t to usable
        this.estimatedCSUsableRules(usable, s, t);

        return ImmutableCreator.create(usable);
    }

    public final void estimatedCSUsableRules(Set<Rule> usable, Rule l_to_r) {
        if (Globals.useAssertions) {
            assert (l_to_r.equals(l_to_r
                    .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX)));
        }
        Set<TRSTerm> s = new LinkedHashSet<TRSTerm>();
        s.add(l_to_r.getLeft());
        TRSTerm t = l_to_r.getRight();
        this.estimatedCSUsableRules(usable, s, t);
    }

    private final void estimatedCSUsableRules(Set<Rule> usable, Set<TRSTerm> s,
            TRSTerm t) {
        if (t.isVariable()) {
            this.estimatedCSUsableRules(usable, s, (TRSVariable) t);
        } else {
            this.estimatedCSUsableRules(usable, s, (TRSFunctionApplication) t);
        }
    }

    /**
     *
     * @param usable
     * @param s
     *            in third standard prefix form
     * @param t
     *            in third standard prefix form
     */
    private final void estimatedCSUsableRules(Set<Rule> usable, Set<TRSTerm> s,
            TRSFunctionApplication t) {
        // step 1.
        FunctionSymbol f = t.getRootSymbol();
        ImmutableSet<Integer> map = this.mu.getMap().get(f);

        // build capT = f(t'_i,\dots,t'_n)
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (int i = 0; i < f.getArity(); ++i) {
            TRSTerm t_i = t.getArgument(i);
            if (map.contains(i)) {
                // t'_i = ECapMu(t_i)
                TRSTerm tPrime_i = this.eCapMu.capMu(this.mu, this.q, this.genR, this.innermost, s, t_i);
                args.add(tPrime_i);
            } else {
                args.add(t_i);
            }
        }
        TRSTerm capT = TRSTerm.createFunctionApplication(f, ImmutableCreator
                .create(args));
        // capTStd in first normal form
        TRSTerm capTStd = capT.getStandardRenumbered();

        // step 2.
        for (Integer i : map) {
            TRSTerm t_i = t.getArgument(i);
            this.estimatedCSUsableRules(usable, s, t_i);
        }

        Set<Rule> rules = this.symbolToRules.get(f);
        if (rules == null) {
            return;
        }

        for (Rule l_to_r : rules) {
            if (usable.contains(l_to_r)) {
                continue;
            }

            Rule stdRule = l_to_r
                    .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            TRSFunctionApplication l = stdRule.getLeft();

            TRSSubstitution delta = l.getMGU(capTStd);
            if (delta == null) {
                continue;
            }

            // build set of l_i terms for i in mu(f)
            Set<TRSTerm> lis = new LinkedHashSet<TRSTerm>();
            for (Integer i : map) {
                TRSTerm l_i = l.getArgument(i);
                lis.add(l_i);
            }

            // check if delta instantiates S and l_i to normal forms
            for (TRSTerm u : s) {
                if (!this.mu.inQMuNormalForm(this.q, u.applySubstitution(delta))) {
                    continue;
                }
            }
            for (TRSTerm l_i : lis) {
                if (!this.mu.inQMuNormalForm(this.q, l_i.applySubstitution(delta))) {
                    continue;
                }
            }

            // so every l_i and s is in Q-mu-normal form
            usable.add(l_to_r);

            // step 3.
            this.estimatedCSUsableRules(usable, lis, stdRule.getRight());
        }
    }

    private final void estimatedCSUsableRules(Set<Rule> usable, Set<TRSTerm> s,
            TRSVariable x) {
        // step 4.
        if (this.innermost) {
            for (TRSTerm u : s) {
                // if x is from the replacing variables of u, we know it is
                // instanciated to NFMu(Q)
                if (this.mu.getReplacingVariables(u).contains(x)) {
                    return;
                }
            }
        }

        // not innermost or x is no subterm of a term of s
        usable.addAll(this.r);
    }
}
