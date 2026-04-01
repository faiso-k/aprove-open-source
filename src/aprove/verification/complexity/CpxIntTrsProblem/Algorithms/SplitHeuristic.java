package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.RationalPolynomial.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class SplitHeuristic {

    public static RatPolImplication split(RatPolImplication impli) throws SplitHeuristicNotApplicableException {
        ImmutableSet<RationalPolynomial> cons = impli.consequences;
        ImmutableSet<String> existentialVars = impli.existentialVars;
        ImmutableSet<RationalPolynomial> premises = impli.premises;
        Set<RationalPolynomial> resultsAkk = new LinkedHashSet<>();
        for (RationalPolynomial p : cons) {
            SplitHeuristic.split(p, existentialVars, premises, resultsAkk);
        }
        return new RatPolImplication(existentialVars, premises, ImmutableCreator.create(resultsAkk));
    }

    private static void split(
        final RationalPolynomial geZero,
        final ImmutableSet<String> existentialVars,
        final Set<RationalPolynomial> premises,
        final Set<RationalPolynomial> resultsAkk) throws SplitHeuristicNotApplicableException
    {
        if (geZero.isLinearOnVars(existentialVars)) {
            resultsAkk.add(geZero);
            return;
        }
        Pair<RationalPolynomial, RationalPolynomial> split = SplitHeuristic.findGoodSplits(geZero, premises, existentialVars);
        if (split == null) {
            throw new SplitHeuristicNotApplicableException();
        }
        SplitHeuristic.split(split.x, existentialVars, premises, resultsAkk);
        SplitHeuristic.split(split.y, existentialVars, premises, resultsAkk);
    }

    private static <T> boolean intersects(final Set<T> a, final Set<T> b) {
        for (T e : a) {
            if (b.contains(e)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tries to find Polynomials {@code p} and {@code r}, such that {@code t} = {@code p} * {@code t} + {@code r}.
     * @param t
     * @return
     */
    static private Set<Pair<RationalPolynomial, RationalPolynomial>> splitPolynomial(
        final RationalPolynomial p,
        final RationalPolynomial t)
    {
        Set<Pair<RationalPolynomial, RationalPolynomial>> rv = new LinkedHashSet<>();
        if (t.numberOfMonomials() == 1) {
            Monomial tmon = t.iterator().next();
            Set<Monomial> r = new LinkedHashSet<>();
            Set<Monomial> q = new LinkedHashSet<>();
            for (Monomial m : p) {
                Monomial d = m.divide(tmon);
                if (d != null) {
                    q.add(d);
                } else {
                    r.add(m);
                }
            }
            rv.add(new Pair<>(RationalPolynomial.createAsSumOfMonomials(r), RationalPolynomial
                .createAsSumOfMonomials(q)));
        }
        for (Monomial thisMonsCand : p) {
            for (Monomial divMonsCand : t) {
                Pair<RationalPolynomial, RationalPolynomial> rq = SplitHeuristic.split(p, thisMonsCand, t, divMonsCand);
                if (rq == null) {
                    continue;
                }
                RationalPolynomial r = rq.x;
                RationalPolynomial q = rq.y;
                rv.add(new Pair<>(r, q));
            }
        }

        if (Globals.useAssertions) {
            for (Pair<RationalPolynomial, RationalPolynomial> rq : rv) {
                RationalPolynomial r = rq.x;
                RationalPolynomial q = rq.y;
                RationalPolynomial randqdiv = r.add(t.multiply(q));
                assert p.equals(randqdiv);
            }
        }
        return rv;
    }

    /**
     * Return two RationalPolynomials q and r, such that thisMons = q * divMons + r.
     * @param thisMons
     * @param thisMonsCand
     * @param divMons
     * @param divMonsCand
     * @return
     */
    private static Pair<RationalPolynomial, RationalPolynomial> split(
        final RationalPolynomial t,
        final Monomial thisMonsCand,
        final RationalPolynomial divMons,
        final Monomial divMonsCand)
    {
        Monomial q = thisMonsCand.divide(divMonsCand);
        if (q == null) {
            return null;
        }

        RationalPolynomial thisWOcand = t.add(new RationalPolynomial(thisMonsCand.negate()));
        RationalPolynomial divWOcand = divMons.add(new RationalPolynomial(divMonsCand.negate()));

        Monomial qneg = q.negate();
        RationalPolynomial divWOcandq = divWOcand.multiply(qneg);
        RationalPolynomial r = thisWOcand.add(divWOcandq);

        return new Pair<>(r, new RationalPolynomial(q));
    }

    /**
     * returns true iff a is "easier" to solve than b.
     * @param a
     * @param b
     * @param universallyQuantified
     * @return
     */
    private static int compareHardness(
        final RationalPolynomial a,
        final RationalPolynomial b,
        final Set<String> existentiallyQuantified)
    {
        int va = SplitHeuristic.countDifferentQuantifiedIndefParts(a, existentiallyQuantified);
        int vb = SplitHeuristic.countDifferentQuantifiedIndefParts(b, existentiallyQuantified);
        return Integer.compare(va, vb);
    }

    private static int countDifferentQuantifiedIndefParts(
        final RationalPolynomial pol,
        final Set<String> existentiallyQuantified)
    {
        Set<Map<String, Integer>> quantifiedIndefs = new LinkedHashSet<>();
        for (Monomial mon : pol) {
            Map<String, Integer> exps = new LinkedHashMap<>();
            exps.putAll(mon.indefinitePart.getExponents());
            Iterator<Entry<String, Integer>> it = exps.entrySet().iterator();
            while (it.hasNext()) {
                Entry<String, Integer> n = it.next();
                if (existentiallyQuantified.contains(n.getKey())) {
                    it.remove();
                }
            }
            quantifiedIndefs.add(exps);
        }
        return quantifiedIndefs.size();
    }

    private static Pair<RationalPolynomial, RationalPolynomial> findGoodSplits(
        final RationalPolynomial geZero,
        final Set<RationalPolynomial> constraints,
        final Set<String> existentiallyQuantified)
    {
        Set<Pair<RationalPolynomial, RationalPolynomial>> candidates = new LinkedHashSet<>();
        Set<String> polVars = geZero.getVariables();
        for (RationalPolynomial constraint : constraints) {
            Set<String> constrVars = constraint.getVariables();
            if (!SplitHeuristic.intersects(polVars, constrVars)) {
                continue;
            }
            candidates.addAll(SplitHeuristic.splitPolynomial(geZero, constraint));
        }
        Pair<RationalPolynomial, RationalPolynomial> bestPair = null;

        for (Pair<RationalPolynomial, RationalPolynomial> cand : candidates) {
            RationalPolynomial p1 = cand.x;
            RationalPolynomial p2 = cand.y;

            // if one of the split polynomials is at least as "hard" as geZero, skip this pair
            if (SplitHeuristic.compareHardness(p1, geZero, existentiallyQuantified) >= 0
                || SplitHeuristic.compareHardness(p2, geZero, existentiallyQuantified) >= 0)
            {
                continue;
            }

            // to get the best of all pairs we only compare the first component, not to discriminate strong partitions
            if (bestPair != null && SplitHeuristic.compareHardness(p1, bestPair.x, existentiallyQuantified) >= 0) {
                continue;
            }
            bestPair = cand;
        }
        return bestPair;
    }
}
