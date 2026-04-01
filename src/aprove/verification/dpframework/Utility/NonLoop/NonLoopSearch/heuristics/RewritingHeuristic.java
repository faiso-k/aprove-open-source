package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class RewritingHeuristic {

    private static final int maxSteps = 16;

    public static Set<ProofedRule> rewritingHeuristic(final ProofedRule pr) {

        final Set<ProofedRule> rv = new LinkedHashSet<>();

        final ImmutableSet<Rule> R = pr.getR();

        final PatternRule lr = pr.getPatternRule();
        final PatternTerm pat = lr.getRhs();

        // try base first
        {
            final TRSTerm rBase = pat.getT();
            final ImmutableList<Pair<Position, Rule>> seq =
                RewritingHeuristic.buildRewriteSeq(RewritingHeuristic.maxSteps, rBase, R, false);
            if (seq != null) {
                rv.add(RewriteT.create(pr, seq));
            }
        }

        // try sigma next
        {
            final TRSSubstitution sigma = pat.getSigma();
            for (final Entry<TRSVariable, ? extends TRSTerm> e : sigma.toMap().entrySet()) {
                final ImmutableList<Pair<Position, Rule>> seq =
                    RewritingHeuristic.buildRewriteSeq(RewritingHeuristic.maxSteps, e.getValue(), R, true);
                if (seq != null) {
                    rv.add(RewriteSigma.create(pr, e.getKey(), seq));
                }
            }
        }

        // try mu last
        {
            final TRSSubstitution mu = pat.getMu();
            for (final Entry<TRSVariable, ? extends TRSTerm> e : mu.toMap().entrySet()) {
                final TRSVariable x = e.getKey();
                final TRSTerm t = e.getValue();
                ImmutableList<Pair<Position, Rule>> seq =
                    RewritingHeuristic.buildRewriteSeq(RewritingHeuristic.maxSteps, t, R, true);
                if (seq != null) {
                    rv.add(RewriteMu.create(pr, x, seq));
                } else {
                    // try to instantiate possible matcher
                    final List<TRSSubstitution> inst = RewritingHeuristic.getPossibleInstantiations(t, R);

                    // now try to instantiate mu with the possible matchers
                    for (final TRSSubstitution sigma : inst) {
                        ProofedRule instantiation = InstantiateMu.create(pr, sigma);
                        if (instantiation == null) {
                            continue;
                        }

                        instantiation = Equivalence.createRemoveAllIrrelevant(instantiation);
                        // finally try to find a rewrite seq
                        // for the instantiated pr
                        seq =
                            RewritingHeuristic.buildRewriteSeq(
                                RewritingHeuristic.maxSteps,
                                t.applySubstitution(sigma),
                                R,
                                true
                            );
                        if (seq != null) {
                            rv.add(RewriteMu.create(instantiation, x, seq));
                        }
                    }
                }
            }
        }

        return rv;
    }

    private static List<TRSSubstitution> getPossibleInstantiations(final TRSTerm t, final ImmutableSet<Rule> R) {
        final List<TRSSubstitution> insts = new LinkedList<TRSSubstitution>();

        for (final TRSTerm subt : t.getSubTerms()) {

            if (subt.isVariable()) {
                continue;
            }

            for (final Rule r : R) {
                final TRSSubstitution matcher = t.getMatcher(r.getLeft());
                if (matcher != null) {
                    insts.add(matcher);
                }
            }
        }

        return insts;
    }

    private static ImmutableList<Pair<Position, Rule>> buildRewriteSeq(final int maxDepth,
        final TRSTerm rBase,
        final ImmutableSet<Rule> R,
        final boolean allowRoot) {
        try {
            return
                RewritingHeuristic.buildRewriteSeq(
                    new ArrayDeque<Pair<Position, Rule>>(),
                    maxDepth,
                    rBase,
                    R,
                    allowRoot
                );
        } catch (final CannotNormalizeException e) {
            return null;
        }
    }

    private static ImmutableList<Pair<Position, Rule>> buildRewriteSeq(final Deque<Pair<Position, Rule>> currentList,
        final int maxDepth,
        final TRSTerm t,
        final ImmutableSet<Rule> R,
        final boolean allowRoot) throws CannotNormalizeException {

        if (maxDepth <= 0) {
            throw new CannotNormalizeException();
        }

        boolean isNormal = true;

        for (final Pair<Position, TRSTerm> pt : t.getPositionsWithSubTerms()) {
            final Position pos = pt.x;
            if (pos.isEmptyPosition() && !allowRoot) {
                continue;
            }
            final TRSTerm subterm = pt.y;
            if (subterm.isVariable()) {
                continue;
            }
            for (final Rule rule : R) {
                final TRSSubstitution sigma = rule.getLeft().getMatcher(subterm);
                if (sigma == null) {
                    continue;
                }
                isNormal = false;
                final TRSTerm tPrime = t.replaceAt(pos, rule.getRight().applySubstitution(sigma));
                currentList.add(new Pair<>(pos, rule));
                final ImmutableList<Pair<Position, Rule>> seq =
                    RewritingHeuristic.buildRewriteSeq(currentList, maxDepth - 1, tPrime, R, allowRoot);
                if (seq != null) {
                    return seq;
                }
                currentList.removeLast();
            }
        }

        if (isNormal && currentList.size() != 0) {
            final ArrayList<Pair<Position, Rule>> list = new ArrayList<>();
            list.addAll(currentList);
            return ImmutableCreator.create(list);
        }

        return null;
    }
}
