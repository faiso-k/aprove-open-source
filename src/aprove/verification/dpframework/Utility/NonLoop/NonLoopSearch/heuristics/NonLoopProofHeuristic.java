package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class NonLoopProofHeuristic {

    private static final int MAX_INST = 1;
    private static final int MAX_K = 3;

    public static NonLoopProof isNonTerminating(final ProofedRule lr) {
        return NonLoopProofHeuristic.isNonTerminating(NonLoopProofHeuristic.MAX_K, lr, 0);
    }

    public static NonLoopProof isNonTerminating(final int maxK, final ProofedRule lr, final int countInst) {

        final PatternRule plr = lr.getPatternRule();
        final PatternTerm lhs = plr.getLhs();

        final PatternTerm rhs = plr.getRhs();
        final TRSTerm u = lhs.getT();

        final Set<Position> posv = PatternUtils.usablePositions(u, rhs.getT());// v.getPositions();
        // TODO maybe do some crude approximation of possible positions here
        // to make the following loops faster
        for (int k = 0; k <= maxK; ++k) {
            for (final Position pi : posv) {
                final NonLoopProof nlp = NonLoopProofHeuristic.isNonTerminating(lr, k, pi, countInst);
                if (nlp != null) {
                    return nlp;
                }
            }
        }
        return null;
    }

    private static NonLoopProof isNonTerminating(ProofedRule lr, final int k, final Position pi, int countInst) {

        if (countInst > NonLoopProofHeuristic.MAX_INST) {
            return null;
        }

        lr = lr.getStandardLeft();

        ProofedRule sameLR = PatternUtils.sameVarsDR(lr, pi);
        if (sameLR == null) {
            return null;
        }

        sameLR = PatternUtils.reduceRenamings(sameLR, true);

        final PatternRule plr = sameLR.getPatternRule();
        final PatternTerm lhs = plr.getLhs();
        final TRSSubstitution sigma = lhs.getSigma();
        TRSSubstitution sigmak = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (int i = 0; i < k; ++i) {
            sigmak = sigmak.compose(sigma);
        }
        final TRSSubstitution mu = lhs.getMu();

        final PatternTerm rhs = plr.getRhs();
        final TRSTerm u = lhs.getT();

        final TRSTerm vpi = rhs.getT().getSubterm(pi);

        final Pair<TRSSubstitution, Integer> sigmaSplit = NonLoopProofHeuristic.splitOffSubstitutionWithM(sigma, rhs.getSigma(), true);
        if (sigmaSplit == null) {
            return null;
        }
        final TRSSubstitution sigmaPrime = sigmaSplit.x;

        final Pair<TRSSubstitution, Integer> muSplit = NonLoopProofHeuristic.splitOffSubstitutionWithM(lhs.getMu(), rhs.getMu(), false);
        if (muSplit == null) {
            // one last desperate try
            final TRSSubstitution rho = Utils.unifySubstitutions(lhs.getMu(), rhs.getMu());
            if (rho == null) {
                return null;
            }
            sameLR = InstantiateMu.create(sameLR, rho);
            return NonLoopProofHeuristic.isNonTerminating(sameLR, k, pi, countInst + 1);
        }
        final TRSSubstitution muPrime = muSplit.x;

        if (!Utils.commutative(sigmaPrime, sigma) || !Utils.commutative(sigmaPrime, mu)) {
            return null;
        }

        final TRSTerm usigmak = u.applySubstitution(sigmak);
        final SemiUnification semi = new SemiUnification(usigmak, vpi);

        if (semi.semiUnify()) {
            final Pair<TRSSubstitution, TRSSubstitution> semiUns = semi.getSubstitutions();
            final TRSSubstitution delta2 = semiUns.x;
            final TRSSubstitution delta1 = semiUns.y;

            if (Utils.commutative(delta1, sigma) && Utils.commutative(delta1, mu)
                && Utils.commutative(delta1, sigmaPrime) && Utils.commutative(delta1, muPrime)
                && Utils.commutative(delta2, sigma) && Utils.commutative(delta2, mu)
                && Utils.commutative(delta2, sigmaPrime) && Utils.commutative(delta2, muPrime)) {

                sameLR = InstantiateMu.create(sameLR, delta1);
                TRSSubstitution oldMuL = sameLR.getPatternRule().getLhs().getMu();
                final TRSSubstitution oldMuR = sameLR.getPatternRule().getRhs().getMu();
                sameLR = Equivalence.createSimplifyingMu(sameLR, delta1, oldMuL, delta1, oldMuR);
                oldMuL = sameLR.getPatternRule().getLhs().getMu();
                sameLR = InstantiateMu.create(sameLR, delta2);
                sameLR =
                    Equivalence.createSimplifyingMu(sameLR, delta2, oldMuL, TRSSubstitution.EMPTY_SUBSTITUTION,
                        sameLR.getPatternRule().getRhs().getMu());

                final NonLoopProof nlp =
                    NonLoopProof.create(sameLR, pi, sigmaSplit.y, k, sigmaPrime, muPrime.compose(delta2));

                return nlp;
            }

            // try to instantiate but
            // only if the maximum number of instantiations isn't reached yet
            if (countInst < NonLoopProofHeuristic.MAX_INST) {
                countInst++;

                ProofedRule inst = InstantiateMu.create(sameLR, delta1);
                inst = InstantiateMu.create(inst, delta2);
                inst = SimplifyMuHeuristic.simplifyMu(inst);
                if (!inst.equals(sameLR)) {
                    // try to prove non-termination for the instantiation
                    final NonLoopProof nlp = NonLoopProofHeuristic.isNonTerminating(inst, k, pi, countInst);

                    if (nlp != null) {
                        return nlp;
                    }
                }

                // try to Instantiation with the biggest subsets of delta{1,2}
                // find biggest subset of delta1 which we can instantiate
                final TRSSubstitution delta1Prime = NonLoopProofHeuristic.findBiggestDelta(sameLR, delta1);

                inst = Instantiation.create(sameLR, delta1Prime);

                // try to instantiate biggest subset of delta2 too
                final TRSSubstitution delta2Prime = NonLoopProofHeuristic.findBiggestDelta(inst, delta2);

                inst = Instantiation.create(inst, delta2Prime);

                if (!inst.equals(sameLR)) {
                    return NonLoopProofHeuristic.isNonTerminating(inst, k, pi, countInst);
                }
            }

        }
        return null;
    }

    private static TRSSubstitution findBiggestDelta(final ProofedRule lr, final TRSSubstitution delta1) {
        final Map<TRSVariable, TRSTerm> subsetMap = new LinkedHashMap<>();

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        final Set<TRSVariable> doms = new LinkedHashSet<>();
        doms.addAll(lhs.getSigma().getDomain());
        doms.addAll(lhs.getMu().getDomain());
        doms.addAll(rhs.getSigma().getDomain());
        doms.addAll(rhs.getMu().getDomain());

        for (final Entry<TRSVariable, ? extends TRSTerm> xt : delta1.toMap().entrySet()) {
            final TRSVariable x = xt.getKey();
            final TRSTerm t = xt.getValue();

            final LinkedHashSet<TRSVariable> intersect = new LinkedHashSet<>(doms);
            intersect.retainAll(t.getVariables());

            if (!doms.contains(x) && intersect.isEmpty()) {
                subsetMap.put(x, t);
            }
        }

        return TRSSubstitution.create(ImmutableCreator.create(subsetMap));
    }

    /**
     * Generates a substitution {@link TRSSubstitution mu} and a natural number m,
     * where m > 0, such that<br>
     * {@code sigma^m mu = theta}.
     *
     * @param sigma
     * @param theta
     * @param searchForM
     *            If <tt>false</tt>, only <tt> m=1</tt> is checked.
     * @return {@link TRSSubstitution mu} if it exists, <tt>null</tt> if it doesn't
     */
    private static Pair<TRSSubstitution, Integer> splitOffSubstitutionWithM(final TRSSubstitution sigma,
        final TRSSubstitution theta,
        final boolean searchForM) {

        int m = 1;
        TRSSubstitution sigmaM = sigma;
        int size;

        int nextM = m;
        int nextSize = NonLoopProofHeuristic.sizeOfSubstitution(sigmaM);
        TRSSubstitution nextSigmaM = sigmaM;

        TRSSubstitution mu = null;

        do {
            final TRSSubstitution nextMu = Utils.matchSubstitutions(nextSigmaM, theta);
            if (nextMu == null) {
                break;
            }
            mu = nextMu;
            if (!searchForM) {
                break;
            }

            sigmaM = nextSigmaM;
            m = nextM;
            size = nextSize;

            nextM = m + 1;
            nextSigmaM = sigmaM.compose(sigma);
            nextSize = NonLoopProofHeuristic.sizeOfSubstitution(nextSigmaM);
        } while (nextSize > size);

        if (mu == null) {
            return null;
        }

        if (Globals.useAssertions) {
            TRSSubstitution sigmaMPrime = sigma;
            // apply origSigma m times
            for (int i = 1; i < m; i++) {
                sigmaMPrime = sigmaMPrime.compose(sigma);
            }
            assert sigmaM.compose(mu).equals(theta);
        }

        return new Pair<TRSSubstitution, Integer>(mu, m);
    }

    private static int sizeOfSubstitution(TRSSubstitution sigma) {
        int i = 0;
        for (final TRSTerm u : sigma.toMap().values()) {
            i += u.getSize() + 1;
        }
        return i;
    }

}
