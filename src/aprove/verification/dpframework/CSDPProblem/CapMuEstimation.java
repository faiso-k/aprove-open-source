package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public abstract class CapMuEstimation {

    public CapMuEstimation() {
    }

    protected static class FreshNameGenerator {
        private int next = 1;

        private static final String prefix = TRSTerm.STANDARD_PREFIX;

        public TRSVariable getNextFreshVariable() {
            return TRSTerm.createVariable(FreshNameGenerator.prefix + "_" + this.next++);
        }
    }

    /**
     * Computes an estimated context-sensitive cap function. ([E07 or
     * something]).
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
    public TRSTerm capMu(ReplacementMap mu, QTermSet q, GeneralizedTRS r,
            boolean innermost, Rule s_to_t) {
        FreshNameGenerator gen = new FreshNameGenerator();
        Set<TRSTerm> s = new LinkedHashSet<TRSTerm>();
        s.add(s_to_t.getLeft());
        return this.capMu(mu, q, r, s, s_to_t.getRight(), innermost, gen);
    }

    public TRSTerm capMu(ReplacementMap mu, QTermSet q, GeneralizedTRS r,
            boolean innermost, Set<TRSTerm> s, TRSTerm t) {
        FreshNameGenerator gen = new FreshNameGenerator();
        return this.capMu(mu, q, r, s, t, innermost, gen);
    }

    protected abstract TRSTerm capMu(ReplacementMap mu, QTermSet q,
            GeneralizedTRS r, Set<TRSTerm> s, TRSTerm t, boolean innermost,
            FreshNameGenerator gen);
}