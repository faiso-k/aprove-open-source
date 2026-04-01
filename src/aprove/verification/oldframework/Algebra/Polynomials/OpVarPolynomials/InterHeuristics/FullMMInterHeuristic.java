package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Always use max and min for the symbol f where reasonably possible.
 *
 * @author fuhs
 * @version $Id$
 */
public class FullMMInterHeuristic implements MMInterHeuristic {

    public FullMMInterHeuristic() {
    }

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        else {
            return true;
        }
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        return this.allowMax(f, i, j);
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>(arity*(arity-1)/2);
        for (int i = 0; i < arity; ++i) {
            for (int j = i + 1; j < arity; ++j) {
                Pair<Integer, Integer> ij = new Pair<Integer, Integer>(i, j);
                result.add(ij);
            }
        }
        return result;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return this.getMaxCombinations(f);
    }

    // don't care, just say true regardless of R and P :-)
    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {}

}
