package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Allow negative coefficients for those f that are not constants, i.e.,
 * that have arity > 0.
 *
 * @author fuhs
 */
public class NonConstNCInterHeuristic implements NCInterHeuristic {

    public NonConstNCInterHeuristic() {
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        final int arity = f.getArity();
        return arity > 0;
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f, int i) {
        return this.useNegCoeff(f);
    }

    @Override
    public boolean useNegConst(FunctionSymbol f) {
        return this.useNegCoeff(f);
    }

    @Override
    public void setP(Set<? extends GeneralizedRule> p) {
    }

    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {
    }
}
