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
 * Neg coeffs ok if symbol is defined and occurs in rhs of a DP or
 * if symbol is a head symbol in P (aka "tuple symbol") and lhs of that
 * one of these pairs is embedded in rhs.
 *
 * Neg consts ok if symbol is destructor (e.g., p(s(x)) -> x removes
 *  context s(.) from x, hence we call p a destructor).
 *
 * Allows max(x_i, x_j) in the interpretation of f if:
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - r_1 and r_2 are variables
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is r_2
 * - i != j
 *
 * Min never ok.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class DivHeuristic implements NonMonInterHeuristic {

    private Set<? extends GeneralizedRule> R;
    private Set<? extends GeneralizedRule> P;
    private Set<FunctionSymbol> destructors;

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    private Map<FunctionSymbol, boolean[]> superArgPositionsMax;

    public DivHeuristic() {
        this.resetSuperArgsPositions();
    }

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositionsMax.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        return false;
    }

    @Override
    public boolean allowNegCoeff(FunctionSymbol f) {
        if (CollectionUtils.getRootSymbols(this.R).contains(f)) {
            Set<FunctionSymbol> fSyms = new HashSet<FunctionSymbol>();
            for (GeneralizedRule pRule : this.P) {
                TRSTerm t = pRule.getRight();
                t.collectFunctionSymbols(fSyms);
                if (fSyms.contains(f)) {
                    return true;
                }
            }
        }
        else {
            for (GeneralizedRule pRule : this.P) {
                if (f.equals(pRule.getRootSymbol())) {
                    Constraint<TRSTerm> rGEl = Constraint.create(pRule.getRight(),
                            pRule.getLeft(), OrderRelation.GR);
                    if (EMB.theEMB.solves(rGEl)) {
                        return true;
                    }
                }
            }

        }
        return false;
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
        int arity = f.getArity();
        if (arity < 2) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>();
        boolean[] allowedArgsForF = this.superArgPositionsMax.get(f);
        if (allowedArgsForF != null) {
            for (int i = 0; i < arity; ++i) {
                if (allowedArgsForF[i]) {
                    for (int j = i + 1; j < arity; ++j) {
                        if (allowedArgsForF[j]) {
                            Pair<Integer, Integer> ij = new Pair<Integer, Integer>(i, j);
                            result.add(ij);
                        }
                    }
                }
            }
        }
        return result;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.resetSuperArgsPositions();
        this.addNewDataForMax(r);
        this.addNewDataForMax(p);
        this.P = p;
        this.R = r;
        this.initDestructors();
    }

    private void resetSuperArgsPositions() {
        this.superArgPositionsMax = new HashMap<FunctionSymbol, boolean[]>();
    }


    private void addNewDataForMax(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSFunctionApplication l = rule.getLeft();
            Collection<Pair<Position, TRSTerm>> lPosWithSubterms = l.getPositionsWithSubTerms();
            TRSTerm r = rule.getRight();

            for (Pair<Position, TRSTerm> lPosWithSubterm : lPosWithSubterms) {
                TRSTerm subterm = lPosWithSubterm.y;
                Position pos = lPosWithSubterm.x;
                if (subterm.equals(r) && ! pos.isEmptyPosition()) {
                    // Got one! Now save the info for the function symbol
                    // directly above.
                    int j = pos.lastIndex();
                    pos = pos.shorten(1);
                    // every non-leaf of a term is a FunctionApplication,
                    // so the following cast should be safe
                    TRSFunctionApplication gApp = (TRSFunctionApplication) l.getSubterm(pos);
                    FunctionSymbol g = gApp.getRootSymbol();
                    if (r.isVariable()) {
                        this.putMaxArg(g, j);
                    }
                }
            }
        }
    }

    private void putMaxArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositionsMax.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositionsMax.put(f, positions);
    }


    private void initDestructors() {
        // reset possibly invalid computed values
        this.destructors = new LinkedHashSet<FunctionSymbol>();
        for (GeneralizedRule rule : this.R) {
            TRSFunctionApplication lhs = rule.getLeft();
            FunctionSymbol f = lhs.getRootSymbol();
            if (f.getArity() == 1) {
                TRSTerm rhs = rule.getRight();
                if (lhs.hasProperSubterm(rhs)) {
                    this.destructors.add(f);
                }
            }
        }
    }
}
