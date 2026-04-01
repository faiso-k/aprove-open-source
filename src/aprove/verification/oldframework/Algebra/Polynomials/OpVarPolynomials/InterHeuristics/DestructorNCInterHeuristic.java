package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Allow negative coefficients for those f which are unary and for which
 * there are rules f( C[t] ) -> t for some (possibly empty) context C
 * and some term t, i.e., the rhs of some rule with f at its root occurs
 * in the lhs.
 *
 * Instances of this class may only be accessed by at most one thread at a time.
 *
 * @author fuhs
 * @version $Id$
 */
public class DestructorNCInterHeuristic implements NCInterHeuristic {

    private Map<? extends GeneralizedRule, QActiveCondition> R;
    private Set<FunctionSymbol> destructors;

    public DestructorNCInterHeuristic() {
        this.R = null;
        this.destructors = new HashSet<FunctionSymbol>();
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        return this.destructors.contains(f);
    }

    @Override
    public void setP(Set<? extends GeneralizedRule> p) {
        // P does not matter here.
    }

    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {
        this.R = r;

        // reset possibly invalid computed values
        this.destructors.clear();
        for (Entry<? extends GeneralizedRule, QActiveCondition> e : this.R.entrySet()) {
            GeneralizedRule rule = e.getKey();
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

    @Override
    public boolean useNegCoeff(FunctionSymbol f, int i) {
        return this.useNegCoeff(f);
    }

    @Override
    public boolean useNegConst(FunctionSymbol f) {
        return this.useNegCoeff(f);
    }
}
