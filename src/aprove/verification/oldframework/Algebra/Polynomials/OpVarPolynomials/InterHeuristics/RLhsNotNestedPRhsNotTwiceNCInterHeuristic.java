package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;
import java.util.Map.Entry;

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
public class RLhsNotNestedPRhsNotTwiceNCInterHeuristic implements NCInterHeuristic {

    private Set<? extends GeneralizedRule> P;
    private Map<? extends GeneralizedRule, QActiveCondition> R;

    private Set<FunctionSymbol> definedSymbols;
    private List<Map<FunctionSymbol, Integer>> pRhsSymbolCount;
    private List<Map<FunctionSymbol, Integer>> rLhsSymbolCount;

    private Map<FunctionSymbol, Boolean> cache; // currently unbounded

    public RLhsNotNestedPRhsNotTwiceNCInterHeuristic() {
        this.P = null;
        this.R = null;
        this.definedSymbols = null;
        this.pRhsSymbolCount = null;
        this.rLhsSymbolCount = null;
        this.cache = new HashMap<FunctionSymbol, Boolean>();
    }

    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        Boolean cachedValue = this.cache.get(f);
        if (cachedValue == null) {
            boolean result = false;

            // check R:
            // * is f a defined symbol?
            if (this.definedSymbols == null) {
                this.computeDefinedSymbols();
            }
            if (this.definedSymbols.contains(f)) {

                // * does f occur twice in some lhs?
                if (this.rLhsSymbolCount == null) {
                    this.computeRLhsSymbolCount();
                }
                boolean fOccursTooOftenInRLhs = false;
                for (Map<FunctionSymbol, Integer> fSymCount : this.rLhsSymbolCount) {
                    Integer i = fSymCount.get(f);
                    if (i != null) {
                        if (i > 1) {
                            fOccursTooOftenInRLhs = true;
                            break;
                        }
                    }
                }

                if (! fOccursTooOftenInRLhs) {
                    // check P:
                    // does f occur in some rhs, but never more than once?
                    if (this.pRhsSymbolCount == null) {
                        this.computePRhsSymbolCount();
                    }

                    boolean fOccursInSomeRhsOfP = false;
                    boolean fOccursTooOftenInPRhs = false;
                    for (Map<FunctionSymbol, Integer> fSymCount : this.pRhsSymbolCount) {
                        Integer i = fSymCount.get(f);
                        if (i != null) {
                            if (i > 0) {
                                fOccursInSomeRhsOfP = true;
                                if (i > 1) {
                                    fOccursTooOftenInPRhs = true;
                                    break;
                                }
                            }
                        }
                    }

                    result = (! fOccursTooOftenInPRhs) && fOccursInSomeRhsOfP;
                }
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

    private void computeRLhsSymbolCount() {
        this.rLhsSymbolCount = new ArrayList<Map<FunctionSymbol, Integer>>(this.R.size());
        for (Entry<? extends GeneralizedRule, QActiveCondition> ruleAndCond : this.R.entrySet()) {
            TRSFunctionApplication lhs = ruleAndCond.getKey().getLeft();
            Map<FunctionSymbol, Integer> fSymCount = lhs.getFunctionSymbolCount();
            this.rLhsSymbolCount.add(fSymCount);
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
        this.rLhsSymbolCount = null;
        this.cache.clear();
    }
}
