package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A MMInterHeuristic (Max Min Interpretation Heuristic) states
 * whether for given P and R, a function symbol f may be interpreted using
 * also with max or with min.
 *
 * @author fuhs
 * @version $Id$
 */
public interface MMInterHeuristic {

    /**
     * @param f - a function symbol
     * @param i
     * @param j
     * @return whether we are allowed to consider the max of the
     *  i-th and the j-th argument in the interpretation
     *  of f(x_0, ..., x_{n-1})
     */
    //public abstract boolean allowMax(FunctionSymbol f, int i, int j);

    /**
     * @param f - a function symbol
     * @param i
     * @param j
     * @return whether we are allowed to consider the min of the
     *  i-th and the j-th argument in the interpretation
     *  of f(x_0, ..., x_{n-1})
     */
    //public abstract boolean allowMin(FunctionSymbol f, int i, int j);

    /**
     * @param f
     * @return all pairs of arguments whose max should be part
     *  of the interpretation of f
     */
    public abstract Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f);

    /**
     * @param f
     * @return all pairs of arguments whose min should be part
     *  of the interpretation of f
     */
    public abstract Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f);

    /**
     * @param p - P component of the analyzed DP problem
     * @param r - rules of the R component of the analyzed DP problem
     */
    public abstract void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r);
}
