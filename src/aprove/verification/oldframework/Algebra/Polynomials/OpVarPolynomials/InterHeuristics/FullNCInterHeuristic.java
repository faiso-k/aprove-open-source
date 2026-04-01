package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Always use negative coefficients for the symbol f.
 *
 * @author fuhs
 * @version $Id$
 */
public class FullNCInterHeuristic implements NCInterHeuristic {

    public FullNCInterHeuristic() {
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        return true;
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f, int i) {
        return this.useNegCoeff(f);
    }

    @Override
    public boolean useNegConst(FunctionSymbol f) {
        return this.useNegCoeff(f);
    }

    // don't care, just say true regardless of R and P :-)
    @Override
    public void setP(Set<? extends GeneralizedRule> p) {}
    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {}
}
