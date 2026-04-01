package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Filters everything, which is not int
 * @author Martin Pluecker
 */
public class IdpFreeVarFilterHeuristic implements IIDPFilterHeuristic {

    protected final Map<IDPRuleAnalysis, Map<FunctionSymbol, ImmutableCollection<Integer>>> cache;

    @ParamsViaArgumentObject
    public IdpFreeVarFilterHeuristic() {
        this.cache = new LinkedHashMap<IDPRuleAnalysis, Map<FunctionSymbol, ImmutableCollection<Integer>>>();
    }

    @Override
    public ImmutableCollection<Integer> getFilteredPositions(
            IDPRuleAnalysis ruleAnalysis, FunctionSymbol f) {
        Map<FunctionSymbol, ImmutableCollection<Integer>> map = this.getMap(ruleAnalysis);
        return map.get(f);
    }

    protected Map<FunctionSymbol, ImmutableCollection<Integer>> getMap(
            IDPRuleAnalysis ruleAnalysis) {
        synchronized(this.cache) {
            Map<FunctionSymbol, ImmutableCollection<Integer>> map = this.cache.get(ruleAnalysis);
            if (map == null) {
                this.fillCache(ruleAnalysis);
                map = this.cache.get(ruleAnalysis);
            }
            return map;
        }
    }

    protected void fillCache(IDPRuleAnalysis ruleAnalysis) {
        CollectionMap<FunctionSymbol, Integer> filter = new CollectionMap<FunctionSymbol, Integer>();

        for (GeneralizedRule rule : ruleAnalysis.getRules()) {
            Set<TRSVariable> freeVariables = new LinkedHashSet<TRSVariable>(rule.getRight().getVariables());
            freeVariables.removeAll(rule.getLeft().getVariables());
            if (!freeVariables.isEmpty()) {
                this.collectVariables(rule.getRight(), new ArrayList<Pair<FunctionSymbol, Integer>>(), filter, freeVariables);
            }
        }

        ImmutableSet<FunctionSymbol> fss = ruleAnalysis.getFunctionSymbols();
        Map<FunctionSymbol, boolean[]> usedPositions = new LinkedHashMap<FunctionSymbol, boolean[]>();
        for (FunctionSymbol fs : fss) {
            usedPositions.put(fs, new boolean[fs.getArity()]);
        }


        Map<FunctionSymbol, ImmutableCollection<Integer>> res = new LinkedHashMap<FunctionSymbol, ImmutableCollection<Integer>>();
        for (Map.Entry<FunctionSymbol, Collection<Integer>> entry : filter.entrySet()) {
            res.put(entry.getKey(), ImmutableCreator.create(ImmutableCreator.create(entry.getValue())));
        }
        this.cache.put(ruleAnalysis, res);
    }

    protected void collectVariables(TRSTerm t, List<Pair<FunctionSymbol, Integer>> currentPath, CollectionMap<FunctionSymbol, Integer> filter, Set<TRSVariable> freeVariables) {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            if (freeVariables.contains(v)) {
                for (Pair<FunctionSymbol, Integer> pos : currentPath) {
                    filter.add(pos.x, pos.y);
                }
            }
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication) t;
            FunctionSymbol fs = fa.getRootSymbol();
            ImmutableList<TRSTerm> arguments = fa.getArguments();
            for (int i = arguments.size() -1; i>=0; i--) {
                currentPath.add(new Pair<FunctionSymbol, Integer>(fs, i));
                this.collectVariables(arguments.get(i), currentPath, filter, freeVariables);
                currentPath.remove(currentPath.size()-1);
            }
        }
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap,
            VerbosityLevel verbosityLevel) {
        return "IdpFreeVarFilterHeuristic";
    }

}
