package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class PatternUtils {

    /**
     * lr = s\sigma_s\mu_s -> t \sigma_t\mu_t<br>
     * <br>
     * Tries to find a substitution newMu such that:<br>
     * s\theta\sigma_s newMu -> .... if {@code inLhs} = <tt>true</tt><br>
     * or<br>
     * ... -> t\theta\sigma_t newMu if {@code inLhs} = <tt>false</tt>
     *
     * @param lr
     *            The ProofedRule to "rename".
     * @param theta
     *            Try to apply this "renaming".
     * @param inLhs
     *            If <tt>true</tt>, try to "rename" the left-hand side,
     *            otherwise right-hand side.
     * @return
     */
    public static ProofedRule tryToRename(ProofedRule lr, final TRSSubstitution theta, final boolean inLhs) {

        final Map<TRSVariable, TRSTerm> newMuMap = new LinkedHashMap<>();

        final PatternRule pRule = lr.getPatternRule();

        PatternTerm pt;
        if (inLhs) {
            pt = pRule.getLhs();
        } else {
            pt = pRule.getRhs();
        }

        final TRSSubstitution mu = pt.getMu();

        final Set<TRSVariable> doms = new LinkedHashSet<>(theta.getDomain());
        doms.addAll(mu.getDomain());

        for (final TRSVariable x : doms) {
            final TRSTerm xTheta = x.applySubstitution(theta);
            final TRSTerm xMu = x.applySubstitution(mu);

            final TRSSubstitution matcher = xTheta.getMatcher(xMu);
            if (matcher == null) {
                return null;
            }

            // put the matcher into the new mu
            newMuMap.putAll(matcher.toMap());
        }

        TRSSubstitution muLPrime;
        TRSSubstitution muLnew;
        TRSSubstitution muRPrime;
        TRSSubstitution muRnew;

        if (inLhs) {
            muLPrime = theta;
            muLnew = TRSSubstitution.create(ImmutableCreator.create(newMuMap));
            muRPrime = TRSSubstitution.EMPTY_SUBSTITUTION;
            muRnew = pRule.getRhs().getMu();
        } else {
            muLPrime = TRSSubstitution.EMPTY_SUBSTITUTION;
            muLnew = pRule.getLhs().getMu();
            muRPrime = theta;
            muRnew = TRSSubstitution.create(ImmutableCreator.create(newMuMap));
        }

        lr = Equivalence.createSimplifyingMu(lr, muLPrime, muLnew, muRPrime, muRnew);

        if (lr == null) {
            return null;
        }

        return Equivalence.createRemoveAllIrrelevant(lr);
    }

    public static ProofedRule sameVarsDR(ProofedRule st, final Position pi) {
        PatternRule pr = st.getPatternRule();

        PatternTerm lhs = pr.getLhs();
        final TRSTerm s = lhs.getT();
        Set<TRSVariable> dvS = lhs.getDomainVariables();

        PatternTerm rhs = pr.getRhs();
        final TRSTerm t = rhs.getT();
        Set<TRSVariable> dvT = rhs.getDomainVariables();

        final Pair<TRSSubstitution, TRSSubstitution> theta = Utils.findSubstitutions(s, t.getSubterm(pi));

        final TRSSubstitution thetaS = theta.x;
        final TRSSubstitution thetaT = theta.y;

        pr = st.getPatternRule();
        lhs = pr.getLhs();
        dvS = lhs.getDomainVariables();
        rhs = pr.getRhs();
        dvT = rhs.getDomainVariables();

        final TRSSubstitution kappaS = PatternUtils.buildKappa(dvT, thetaS);
        final TRSSubstitution kappaT = PatternUtils.buildKappa(dvS, thetaT);
        if (kappaS == null || kappaT == null) {
            return null;
        }

        st = Equivalence.createDomainRenaming(st, kappaS, kappaT);

        if (st == null) {
            return null;
        }

        st = SimplifyMuHeuristic.simplifyMu(st);

        st = Equivalence.createRemoveAllIrrelevant(st);

        return st;
    }

    /**
     * { x/y | x \in dv, {y} = V(x\theta) \cap dv }
     *
     * @param dv1
     * @param dv2
     * @param theta
     * @return
     */
    private static TRSSubstitution buildKappa(final Set<TRSVariable> dv, final TRSSubstitution theta) {
        final Map<TRSVariable, TRSVariable> kappaMap = new LinkedHashMap<>();

        for (final TRSVariable x : theta.getDomain()) {
            final Set<TRSVariable> vars = x.applySubstitution(theta).getVariables();
            vars.retainAll(dv);

            if (vars.size() < 1) {
                continue;
            }

            if (vars.size() > 1) {
                return null;
            }

            kappaMap.put(x, vars.iterator().next());
        }

        return TRSSubstitution.create(ImmutableCreator.create(kappaMap));
    }

    public static Set<Position> usablePositions(final TRSTerm l, TRSTerm r) {
        final Set<Position> pos = new LinkedHashSet<>();

        r = r.renameVariables(l.getVariables());

        for (final Position pi : Utils.getNonVarPos(r)) {
            if (r.getSubterm(pi).unifies(l)) {
                pos.add(pi);
            }
        }
        return pos;
    }

    public static ProofedRule reduceRenamings(ProofedRule lr, final boolean firstLhs) {

        PatternTerm pt = firstLhs ? lr.getPatternRule().getLhs() : lr.getPatternRule().getRhs();

        TRSSubstitution renamings = PatternUtils.getRenamings(pt);

        // try to instantiate mu
        ProofedRule temp = InstantiateMu.create(lr, renamings);
        if (temp != null) {
            lr = temp;
            lr = SimplifyMuHeuristic.simplify(lr);
            lr = Equivalence.createRemoveAllIrrelevant(lr);
        }

        pt = !firstLhs ? lr.getPatternRule().getLhs() : lr.getPatternRule().getRhs();

        renamings = PatternUtils.getRenamings(pt);
        temp = InstantiateMu.create(lr, renamings);
        if (temp != null) {
            lr = temp;
            lr = SimplifyMuHeuristic.simplify(lr);
            lr = Equivalence.createRemoveAllIrrelevant(lr);
        }

        return lr;
    }

    private static TRSSubstitution getRenamings(final PatternTerm pt) {
        final Map<TRSVariable, TRSVariable> thetaMap = new LinkedHashMap<>();

        final TRSSubstitution mu = pt.getMu();

        for (final Entry<TRSVariable, ? extends TRSTerm> sub : mu.toMap().entrySet()) {
            if (sub.getValue().isVariable()) {
                thetaMap.put((TRSVariable) sub.getValue(), sub.getKey());
            }
        }

        return TRSSubstitution.create(ImmutableCreator.create(thetaMap));
    }
}
