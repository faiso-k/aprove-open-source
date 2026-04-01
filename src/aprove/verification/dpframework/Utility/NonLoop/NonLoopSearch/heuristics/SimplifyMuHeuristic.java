package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class SimplifyMuHeuristic {

    public static ProofedRule simplifyMu(final ProofedRule lr) {
        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        final Pair<TRSSubstitution, TRSSubstitution> muL = lhs.findEquivalentMus();
        final Pair<TRSSubstitution, TRSSubstitution> muR = rhs.findEquivalentMus();

        return Equivalence.createSimplifyingMu(lr, muL.x, muL.y, muR.x, muR.y);
    }

    public static ProofedRule simplify(ProofedRule lr, final FreshNameGenerator fng) {
        lr = Equivalence.createRemoveAllIrrelevant(lr);
        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        final Pair<TRSSubstitution, TRSSubstitution> muL = SimplifyMuHeuristic.splitMu(lhs, fng);
        final Pair<TRSSubstitution, TRSSubstitution> muR = SimplifyMuHeuristic.splitMu(rhs, fng);

        return Equivalence.createSimplifyingMu(lr, muL.x, muL.y, muR.x, muR.y);
    }

    public static ProofedRule simplify(final ProofedRule lr) {
        final Set<TRSVariable> forbidden = new LinkedHashSet<>(lr.getPatternRule().getAllVariables());
        final FreshNameGenerator gen = new FreshNameGenerator(forbidden, new PrefixNameGenerator("w"));
        return SimplifyMuHeuristic.simplify(lr, gen);
    }

    /**
     * Find rho and the largest rhoPrime, such that mu = rhoPrime rho and
     * rhoPrime commutes with sigma
     *
     * @param pt
     * @param fng
     *            sometimes we need fresh variables to avoid clashes
     * @return
     */
    private static Pair<TRSSubstitution, TRSSubstitution> splitMu(final PatternTerm pt, final FreshNameGenerator fng) {

        final TRSSubstitution sigma = pt.getSigma();
        final TRSSubstitution mu = pt.getMu();
        final ImmutableSet<TRSVariable> sigmaDom = sigma.getDomain();

        final Map<TRSVariable, TRSTerm> rhoMap = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> rhoPrimeMap = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> e : mu.toMap().entrySet()) {
            final TRSVariable x = e.getKey();
            final TRSTerm t = e.getValue();

            final Set<TRSVariable> tVars = t.getVariables();
            tVars.retainAll(sigmaDom);

            final TRSTerm xSigmaMu = x.applySubstitution(sigma).applySubstitution(mu);
            final TRSTerm xMuSigma = x.applySubstitution(mu).applySubstitution(sigma);
            if (xSigmaMu.equals(xMuSigma)) {
                // if sigma and mu commute on x, we are done
                rhoPrimeMap.put(x, t);
            } else {
                if (!sigmaDom.contains(x)) {
                    final Map<TRSVariable, TRSTerm> thetaMap = new LinkedHashMap<>();
                    for (final TRSVariable y : mu.substitute(x).getVariables()) {
                        thetaMap.put(y, TRSTerm.createVariable(fng.getFreshName(y.getName(), true)));
                    }
                    final TRSSubstitution theta = TRSSubstitution.create(ImmutableCreator.create(thetaMap));
                    rhoPrimeMap.put(x, t.applySubstitution(theta));
                    rhoMap.putAll(theta.toMap());
                } else {
                    // otherwise, we have to try how often we need to
                    // instantiate sigma on x to still fit into t
                    TRSTerm xSigmaN = x;
                    TRSSubstitution matcher = xSigmaN.getMatcher(t);
                    final int size = x.getSize();
                    findMatcher: while (true) {
                        final TRSTerm nextxSigmaN = xSigmaN.applySubstitution(sigma);
                        final int nextSize = nextxSigmaN.getSize();
                        if (size >= nextSize) {
                            break;
                        }
                        final TRSSubstitution nextMatcher = nextxSigmaN.getMatcher(t);
                        if (nextMatcher == null) {
                            break;
                        }
                        for (final Entry<TRSVariable, ? extends TRSTerm> match : nextMatcher.toMap().entrySet()) {
                            final TRSVariable y = match.getKey();
                            if (!y.equals(x) && !match.getValue().equals(y.applySubstitution(mu))) {
                                break findMatcher;
                            }
                        }
                        matcher = nextMatcher;
                        xSigmaN = nextxSigmaN;
                    }
                    rhoPrimeMap.put(x, xSigmaN);
                    rhoMap.putAll(matcher.toMap());
                }
            }
        }

        // I think this might fail in contrived situations

        final TRSSubstitution rho = TRSSubstitution.create(ImmutableCreator.create(rhoMap));
        final TRSSubstitution rhoPrime = TRSSubstitution.create(ImmutableCreator.create(rhoPrimeMap));

        // TODO the following is an ugly hack, please remove it when this function is fixed.
        if (!mu.equals(rhoPrime.compose(rho)) || !Utils.commutative(sigma, rhoPrime)) {
            return new Pair<TRSSubstitution, TRSSubstitution>(TRSSubstitution.EMPTY_SUBSTITUTION, pt.getMu());
        }

        if (Globals.useAssertions) {
            assert mu.equals(rhoPrime.compose(rho));
            assert Utils.commutative(sigma, rhoPrime);
        }

        return new Pair<TRSSubstitution, TRSSubstitution>(rhoPrime, rho);
    }

}
