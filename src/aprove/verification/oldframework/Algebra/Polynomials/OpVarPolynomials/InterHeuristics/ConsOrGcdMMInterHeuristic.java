package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Allows max(x_i, x_j) and min(x_i, x_j) in the interpretation of f
 * if ConsMMHeuristic or GcdMMHeuristic do.
 *
 * @author fuhs
 * @version $Id$
 */
public class ConsOrGcdMMInterHeuristic implements MMInterHeuristic {

    private MMInterHeuristic h1, h2;

    public ConsOrGcdMMInterHeuristic() {
        this.h1 = new ConsMMInterHeuristic();
        this.h2 = new  GcdMMInterHeuristic();
    }
    /*
    public boolean allowMax(FunctionSymbol f, int i, int j) {
        return this.h1.allowMax(f, i, j) || this.h2.allowMax(f, i, j);
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        return this.h1.allowMin(f, i, j) || this.h2.allowMin(f, i, j);
    }*/

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        Set<Pair<Integer, Integer>> result = new LinkedHashSet<Pair<Integer, Integer>>();
        result.addAll(this.h1.getMaxCombinations(f));
        result.addAll(this.h2.getMaxCombinations(f));
        return result;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        Set<Pair<Integer, Integer>> result = new LinkedHashSet<Pair<Integer, Integer>>();
        result.addAll(this.h1.getMinCombinations(f));
        result.addAll(this.h2.getMinCombinations(f));
        return result;
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.h1.setPR(p, r);
        this.h2.setPR(p, r);
    }

}
