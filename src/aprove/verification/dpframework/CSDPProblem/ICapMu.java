package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Algorithms to estimate the context-sensitive Cap function.
 *
 * @author fab
 * @version $Id$
 */
public class ICapMu
        extends CapMuEstimation {

    /**
     * Computes the improved estimated context-sensitive Cap function. ([E07 or
     * something]). Implements ICap^mu for only one element in S. Uses supplied
     * Fresh Name Generator.
     *
     * @param mu
     *            the replacement Map
     * @param q
     *            the set of Terms Q
     * @param r
     *            the rules of the generalized TRS R. contained in a mapping
     *            with the root symbol of the lhs as key (for performance). must
     *            be in STANDARD_PREFIX form.
     * @param s_to_t
     *            the rule s -> t, must be in THIRD_STANDARD_PREFIX
     * @param gen
     * @return the term ICap^mu(t), cap variables will be in
     *         SECOND_STANDARD_PREFIX
     */
    @Override
    protected final TRSTerm capMu(ReplacementMap mu, QTermSet q, GeneralizedTRS r,
            Set<TRSTerm> s, TRSTerm t, boolean innermost, FreshNameGenerator gen) {

        if (Globals.useAssertions) {
            for (TRSTerm u : s) {
                assert (u.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            }

            // check that t is i n THIRD_STANDARD_PREFIX
            assert (t.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));

            // check that all lhs of R are in STANDARD_RENUMBERED format
            for (TermPair l_to_r : r) {
                l_to_r.getLeft()
                        .equals(l_to_r.getLhsInStandardRepresentation());
            }
        }

        return ICapMu.iCapMuTerm(mu, q, r, s, t, innermost, gen);
    }

    private static final TRSTerm iCapMuTerm(ReplacementMap mu, QTermSet q,
            GeneralizedTRS r, Set<TRSTerm> s, TRSTerm t, boolean innermost,
            FreshNameGenerator gen) {
        if (t.isVariable()) {
            return ICapMu.iCapMuVariable(s, mu, (TRSVariable) t, innermost, gen);
        } else {
            return ICapMu.iCapMuFunctionApplication(mu, q, r, s,
                    (TRSFunctionApplication) t, innermost, gen);
        }
    }

    private static final TRSTerm iCapMuFunctionApplication(ReplacementMap mu,
            QTermSet q, GeneralizedTRS r, Set<TRSTerm> s, TRSFunctionApplication t,
            boolean innermost, FreshNameGenerator gen) {

        FunctionSymbol f = t.getRootSymbol();
        ImmutableSet<Integer> map = mu.getMap().get(f);
        int n = f.getArity();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(n);

        for (int i = 0; i < n; ++i) {
            TRSTerm t_i = t.getArgument(i);
            if (map.contains(i)) {
                newArgs.add(ICapMu.iCapMuTerm(mu, q, r, s, t_i, innermost, gen));
            } else {
                newArgs.add(t_i);
            }
        }

        TRSFunctionApplication newTerm = TRSTerm.createFunctionApplication(f,
                ImmutableCreator.create(newArgs));

        // no new copy if nothing changed
        if (newTerm.equals(t)) {
            newTerm = t;
        }

        Set<TermPair> rules = r.getSymbolToRule().get(f);
        Set<TermPair> varRules = r.getVarRules();

        // combine all rules with leading f symbol and all rules with variable
        // as lhs
        Iterable<TermPair> allRules;

        if (rules != null && !rules.isEmpty()) {
            allRules = IterableConcatenator.create(rules, varRules);
        } else {
            allRules = varRules;
        }

        rule: for (TermPair l_to_r : allRules) {
            TRSTerm l = l_to_r.getLeft();
            // check that at least one term of s\sigma \cup {l\sigma|_i | i \in
            // \mu(f)} is not in Q-mu-normal form

            TRSSubstitution sigma = l.getMGU(newTerm);
            if (sigma == null) {
                continue;
            }

            // check s\sigma
            for (TRSTerm u : s) {
                if (!mu.inQMuNormalForm(q, u.applySubstitution(sigma))) {
                    continue rule;
                }
            }

            // check t_i for l\sigma = f(t_1, ..., t_n) and i \in \mu(f)
            TRSTerm lsigma = l.applySubstitution(sigma);
            if (Globals.useAssertions) {
                assert (!lsigma.isVariable());
            }

            for (Integer i : map) {
                if (!mu.inQMuNormalForm(q, ((TRSFunctionApplication) lsigma)
                        .getArgument(i))) {
                    continue rule;
                }
            }

            // no non-Q-mu-normal form found
            return gen.getNextFreshVariable();
        }

        return newTerm;
    }

    private static final TRSVariable iCapMuVariable(Set<TRSTerm> s,
            ReplacementMap mu, TRSVariable t, boolean innermost,
            FreshNameGenerator gen) {
        if (innermost) {
            for (TRSTerm u : s) {
                if (mu.getReplacingSubterms(u).contains(t)) {
                    return t;
                }
            }
        }
        return gen.getNextFreshVariable();
    }
}
