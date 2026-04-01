package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Allows max(x_i, x_j) in the interpretation of f if:
 *
 * There exist rules l_1 -> r_1, l_2 -> r_2 \in R \cup P such that
 * - r_1 and r_2 are variables
 * - l_1 is a superterm of f(s_1, ..., s_n), s_i is [a superterm of] r_1
 * - l_2 is a superterm of f(t_1, ..., t_n), t_j is [a superterm of] r_2
 * - i != j
 *
 * Never allows min(x_i, x_j).
 *
 * @author fuhs
 * @version $Id$
 */
public class SubstMMInterHeuristic implements MMInterHeuristic {

    // for a function symbol f, save below which args
    // we have seen some rhs in some corresponding lhs
    private Map<FunctionSymbol, boolean[]> superArgPositions;

    public SubstMMInterHeuristic() {
        this.resetSuperArgsPositions();
    }

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        boolean[] allowedArgsForF = this.superArgPositions.get(f);
        return allowedArgsForF[i] && allowedArgsForF[j];
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        return false;
    }



    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>();
        boolean[] allowedArgsForF = this.superArgPositions.get(f);
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
        this.addNewData(p);
        this.addNewData(r);
    }

    private void resetSuperArgsPositions() {
        this.superArgPositions = new HashMap<FunctionSymbol, boolean[]>();
    }

    private void addNewData(Collection<? extends GeneralizedRule> rules) {
        for (GeneralizedRule rule : rules) {
            TRSFunctionApplication l = rule.getLeft();
            Collection<Pair<Position, TRSTerm>> lPosWithSubterms = l.getPositionsWithSubTerms();
            TRSTerm r = rule.getRight();
            if (r.isVariable()) {
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
                        this.putSuperArg(g, j);
                        /*
                    // Got one! Now save the info for the function symbols
                    // on the way to the root.
                    Position pos = lPosWithSubterm.x;
                    while (! pos.isEmptyPosition()) {
                        // for pos = p.j, we get symbol g at position p and
                        // then remember its j-th arg; repeat with pos = p
                        int j = pos.lastIndex();

                        pos = pos.shorten(1);
                        // every non-leaf of a term is a FunctionApplication,
                        // so the following cast should be safe
                        FunctionApplication gApp = (FunctionApplication) l.getSubterm(pos);
                        FunctionSymbol g = gApp.getRootSymbol();
                        putSuperArg(g, j);
                    }
                         */
                    }
                }
            }
        }
    }

    private void putSuperArg(FunctionSymbol f, int i) {
        boolean[] positions = this.superArgPositions.get(f);
        if (positions == null) {
            positions = new boolean[f.getArity()];
            Arrays.fill(positions, false);
        }
        positions[i] = true;
        this.superArgPositions.put(f, positions);
    }
}
