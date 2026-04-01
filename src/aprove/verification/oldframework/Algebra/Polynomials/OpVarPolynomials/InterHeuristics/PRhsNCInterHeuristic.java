package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Allow negative coefficients for those f that are defined symbols in R
 * and that moreover occur in the rhs of P.
 *
 * @author fuhs
 * @version $Id$
 */
public class PRhsNCInterHeuristic implements NCInterHeuristic {

    private Set<? extends GeneralizedRule> P;
    private Map<? extends GeneralizedRule, QActiveCondition> R;

    public PRhsNCInterHeuristic() {
        this.P = null;
        this.R = null;
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        if (CollectionUtils.getRootSymbols(this.R.keySet()).contains(f)) {
            Set<FunctionSymbol> fSyms = new HashSet<FunctionSymbol>();
            for (GeneralizedRule pRule : this.P) {
                TRSTerm t = pRule.getRight();
                t.collectFunctionSymbols(fSyms);
                if (fSyms.contains(f)) {
                    return true;
                }
            }
        }
        return false;
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
        this.P = p;
    }

    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {
        this.R = r;
    }
}
