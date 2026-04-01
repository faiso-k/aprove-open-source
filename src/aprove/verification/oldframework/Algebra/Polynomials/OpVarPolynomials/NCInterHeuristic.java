package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A NCInterHeuristic (Negative Coefficient Interpretation Heuristic) states
 * whether for given P and R, a function symbol f may be interpreted using
 * negative coefficients/constants or just using non-negative ones.
 *
 * @author fuhs
 * @version $Id$
 */
public interface NCInterHeuristic {

    /**
     * @param f
     * @return whether we are allowed to assign negative values to some
     *  coefficient of f
     */
    public abstract boolean useNegCoeff(FunctionSymbol f);

    /**
     * @param f
     * @param i
     * @return whether we are allowed to assign negative values to the
     *  coefficient(s) of variable x_i in f_Pol
     */
    public abstract boolean useNegCoeff(FunctionSymbol f, int i);

    /**
     * @param f
     * @return whether we are allowed to assign negative values to the
     *  constant in f_Pol
     */
    public abstract boolean useNegConst(FunctionSymbol f);

    public abstract void setR(Map<? extends GeneralizedRule, QActiveCondition> r);
    public abstract void setP(Set<? extends GeneralizedRule> p);

}
