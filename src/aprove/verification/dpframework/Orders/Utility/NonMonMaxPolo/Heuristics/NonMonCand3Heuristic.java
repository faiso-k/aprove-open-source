package aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.Heuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.NonMonMaxPolo.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Really quite permissive. :)
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NonMonCand3Heuristic implements NonMonInterHeuristic {

    private Set<FunctionSymbol> defSyms;

    public NonMonCand3Heuristic() {
    }

    @Override
    public boolean allowNegCoeff(FunctionSymbol f) {
        if ((f.getArity() == 2 && this.defSyms.size() == 1 && this.defSyms.contains(f))) {
            return false;
        }
        return true;
    }

    @Override
    public boolean allowNegCoeff(FunctionSymbol f, int i) {
        return this.allowNegCoeff(f);
    }

    @Override
    public boolean allowNegConst(FunctionSymbol f) {
        return f.getArity() > 0;
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMaxCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public Collection<Pair<Integer, Integer>> getMinCombinations(FunctionSymbol f) {
        return java.util.Collections.emptySet();
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
        this.initDefSyms(r);
    }

    private void initDefSyms(Set<? extends GeneralizedRule> r) {
        this.defSyms = CollectionUtils.getRootSymbols(r);
    }
}
