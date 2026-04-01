package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Allow negative coefficients for those f that are defined symbols in R
 * and that moreover occur in some rhs of P. Additionally, we require that
 * there is no rhs of P in which f occurs more than once.
 *
 * Instances of this class may only be accessed by at most one thread at a time.
 *
 * @author fuhs
 * @version $Id$
 */
public class PRhsNotTwiceNCInterHeuristic implements NCInterHeuristic {

    private Set<? extends GeneralizedRule> P;
    private Map<? extends GeneralizedRule, QActiveCondition> R;

    private Set<FunctionSymbol> definedSymbols;
    private List<Map<FunctionSymbol, Integer>> pRhsSymbolCount;

    private Map<FunctionSymbol, Boolean> cache; // currently unbounded

    public PRhsNotTwiceNCInterHeuristic() {
        this.P = null;
        this.R = null;
        this.definedSymbols = null;
        this.pRhsSymbolCount = null;
        this.cache = new HashMap<FunctionSymbol, Boolean>();
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        Boolean cachedValue = this.cache.get(f);
        if (cachedValue == null) {
            boolean result = false;
            if (this.definedSymbols == null) {
                this.computeDefinedSymbols();
            }
            if (this.definedSymbols.contains(f)) {
                if (this.pRhsSymbolCount == null) {
                    this.computePRhsSymbolCount();
                }
                boolean fOccursInSomeRhsOfP = false;
                boolean fOccursTooOften = false;
                for (Map<FunctionSymbol, Integer> fSymCount : this.pRhsSymbolCount) {
                    Integer i = fSymCount.get(f);
                    if (i != null) {
                        if (i > 0) {
                            fOccursInSomeRhsOfP = true;
                            if (i > 1) {
                                fOccursTooOften = true;
                                break;
                            }
                        }
                    }
                }
                result = (! fOccursTooOften) && fOccursInSomeRhsOfP;
            }
            this.cache.put(f, result);
            return result;
        }
        else {
            return cachedValue;
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

    private void computePRhsSymbolCount() {
        this.pRhsSymbolCount = new ArrayList<Map<FunctionSymbol, Integer>>(this.P.size());
        for (GeneralizedRule pRule : this.P) {
            TRSTerm t = pRule.getRight();
            Map<FunctionSymbol, Integer> fSymCount = t.getFunctionSymbolCount();
            this.pRhsSymbolCount.add(fSymCount);
        }
    }

    private void computeDefinedSymbols() {
        this.definedSymbols = CollectionUtils.getRootSymbols(this.R.keySet());
    }

    @Override
    public void setP(Set<? extends GeneralizedRule> p) {
        this.P = p;

        // reset possibly invalid computed values
        this.pRhsSymbolCount = null;
        this.cache.clear();
    }

    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {
        this.R = r;

        // reset possibly invalid computed values
        this.definedSymbols = null;
        this.cache.clear();
    }
}
