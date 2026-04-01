package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Allows max(x_i, x_j) in the interpretation of f
 * if i != j and f is a non-defined symbol in R.
 *
 * Never allows min(x_i, x_j).
 *
 * @author fuhs
 * @version $Id$
 */
public class ConsMMInterHeuristic implements MMInterHeuristic {

    private Set<FunctionSymbol> consSyms;

    public ConsMMInterHeuristic() {}

    public boolean allowMax(FunctionSymbol f, int i, int j) {
        if (i == j || i < 0 || j < 0 || i >= f.getArity() || j >= f.getArity()) {
            return false;
        }
        return this.consSyms.contains(f);
    }

    public boolean allowMin(FunctionSymbol f, int i, int j) {
        return false;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        int arity = f.getArity();
        if (arity < 2 || ! this.consSyms.contains(f)) {
            return java.util.Collections.emptySet();
        }
        List<Pair<Integer, Integer>> result = new ArrayList<Pair<Integer, Integer>>();
        for (int i = 0; i < arity; ++i) {
            for (int j = i + 1; j < arity; ++j) {
                Pair<Integer, Integer> ij = new Pair<Integer, Integer>(i, j);
                result.add(ij);
            }
        }
        return result;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return Collections.emptySet();
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.resetConsSyms();
        this.addNewData(r);
    }

    private void resetConsSyms() {
        this.consSyms = new LinkedHashSet<FunctionSymbol>();
    }

    private <T extends GeneralizedRule> void addNewData(Set<T> rules) {
        RuleAnalysis<T> ruleAnalysis = new RuleAnalysis<T>(ImmutableCreator.create(rules), IDPPredefinedMap.EMPTY_MAP);
        this.consSyms.addAll(ruleAnalysis.getFunctionSymbols());
        this.consSyms.removeAll(ruleAnalysis.getDefinedSymbols());
    }
}
