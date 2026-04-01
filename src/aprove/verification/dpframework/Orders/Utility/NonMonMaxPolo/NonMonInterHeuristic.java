package aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo;

import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A NonMonInterHeuristic (Non-Monotonic Interpretation Heuristic) states
 * whether for given P and R, a function symbol f may be interpreted using
 * negative coefficients or just using non-negative ones, for which arguments
 * max and min may be used, ...
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface NonMonInterHeuristic extends MMInterHeuristic {

    /**
     * Returns whether we are allowed to make some arg position
     * monotonically *de*creasing.
     *
     * @param f
     * @return whether we are allowed to let some x_i occur in a
     *  decreasing way in f_Pol
     */
    public abstract boolean allowNegCoeff(FunctionSymbol f);

    /**
     * Returns whether we are allowed to make arg position i
     * monotonically *de*creasing.
     *
     * @param f
     * @return whether we are allowed to let x_i occur in a
     *  decreasing way in f_Pol
     */
    public abstract boolean allowNegCoeff(FunctionSymbol f, int i);

    /**
     * Returns whether we are allowed to use a negative constant for f.
     *
     * @param f
     * @return whether we are allowed to let x_i occur in a
     *  decreasing way in f_Pol
     */
    public abstract boolean allowNegConst(FunctionSymbol f);

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

}
