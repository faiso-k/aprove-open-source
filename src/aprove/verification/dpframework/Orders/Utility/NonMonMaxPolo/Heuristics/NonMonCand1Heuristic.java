package aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.Heuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Fine-tuned to tackle the div-system from revision 1.57 of the paper
 * (among the other systems from the paper).
 *
 * Neg coeffs ok if symbol is defined and occurs in rhs of a DP and is
 * not (the only def. symbol and of arity 2, i.e., "app"-like) or
 * if symbol is a head symbol in P (aka "tuple symbol") and lhs of that
 * one of these pairs is embedded in rhs. Moreover, symbol must have
 * arity >= 2. TODO rewrite docs
 *
 * Neg consts ok if symbol is destructor (e.g., p(s(x)) -> x removes
 *  context s(.) from x, hence we call p a destructor).
 *
 * Allows max(x_i, x_j) and min(x_i, x_j) in the interpretation of f if
 * Cand1MMInterHeuristic would.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NonMonCand1Heuristic implements NonMonInterHeuristic {

    private Set<? extends GeneralizedRule> R;
    private Set<? extends GeneralizedRule> P;
    private Set<FunctionSymbol> destructors;
    private Set<FunctionSymbol> defSyms;

    private Set<FunctionSymbol> rewritableRhsSyms;

    private Set<FunctionSymbol> pEmb;


    public NonMonCand1Heuristic() {
    }

    @Override
    public boolean allowNegCoeff(FunctionSymbol f) {
        if (f.getArity() < 2 || (f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
            return false;
        }

        // 1) sym is >=2-ary, occurs as root of a rhs redex
        // TODO maybe we should check whether it is def. recursively.
        // or 2) sym is root of a rule l -> r in P where l is emb. in r and
        // where l, r are non-lin
        // TODO only allow those positions as neg that cause the non-linearity
        return this.rewritableRhsSyms.contains(f) || this.pEmb.contains(f);
    }

    @Override
    public boolean allowNegCoeff(FunctionSymbol f, int i) {
        return this.allowNegCoeff(f);
    }

    @Override
    public boolean allowNegConst(FunctionSymbol f) {
        return this.destructors.contains(f);
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.R = r;
        this.P = p;
        this.initDefSyms();
        this.initRewritableRhsSymbols(p, r);
        this.initPEmb();
        this.initDestructors();
    }

    /**
     * @param rules
     */
    private void initRewritableRhsSymbols(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        Set<FunctionSymbol> rewritableSyms = new LinkedHashSet<FunctionSymbol>();
        RewriteChecker rc = new RewriteChecker(CollectionUtils.getLeftHandSides(r));

        for (GeneralizedRule rule : p) {
            TRSTerm t = rule.getRight();
            rc.collectRewritableSymbols(t, rewritableSyms);
        }
        for (GeneralizedRule rule : r) {
            TRSTerm t = rule.getRight();
            rc.collectRewritableSymbols(t, rewritableSyms);
        }
        this.rewritableRhsSyms = rewritableSyms;
    }

    private void initDefSyms() {
        this.defSyms = CollectionUtils.getRootSymbols(this.R);
    }

    /**
     * If there is F(...) -> t in P such that
     * F(...) is embedded t and both are non-linear,
     * then add F to PEmb.
     */
    private void initPEmb() {
        this.pEmb = new LinkedHashSet<FunctionSymbol>();
        for (GeneralizedRule pRule : this.P) {
            TRSFunctionApplication left = pRule.getLeft();
            TRSTerm right = pRule.getRight();
            if (! left.isLinear() && ! right.isLinear()) {
                FunctionSymbol f = left.getRootSymbol();
                Constraint<TRSTerm> rGRl = Constraint.create(right, left, OrderRelation.GR);
                if (EMB.theEMB.solves(rGRl)) {
                    this.pEmb.add(f);
                }
            }
        }
    }

    /**
     * for neg. constants
     */
    private void initDestructors() {
        // reset possibly invalid computed values
        this.destructors = new LinkedHashSet<FunctionSymbol>();
        for (GeneralizedRule rule : this.R) {
            TRSFunctionApplication lhs = rule.getLeft();
            FunctionSymbol f = lhs.getRootSymbol();
            if (f.getArity() == 1) {
                TRSTerm rhs = rule.getRight();
                for (TRSTerm t : lhs.getArguments()) { // no id(x) -> x, please!
                    if (t.hasProperSubterm(rhs)) {
                        this.destructors.add(f);
                        break;
                    }
                }
            }
        }
    }
}
