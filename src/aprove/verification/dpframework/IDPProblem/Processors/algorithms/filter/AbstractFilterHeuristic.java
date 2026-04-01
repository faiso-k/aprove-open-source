package aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public abstract class AbstractFilterHeuristic implements IIDPFilterHeuristic {


    protected static Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.AbstractFilterHeuristic");

    protected final Map<IDPRuleAnalysis, Map<FunctionSymbol, ImmutableCollection<Integer>>> cache;
    protected final boolean filterRelations;

    @ParamsViaArgumentObject
    public AbstractFilterHeuristic(Arguments arguments) {
        this.cache = new LinkedHashMap<IDPRuleAnalysis, Map<FunctionSymbol, ImmutableCollection<Integer>>>();
        this.filterRelations = arguments.filterRelations;
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
        IDPPredefinedMap predefinedMap = ruleAnalysis.getPreDefinedMap();
        Map<GeneralizedRule, Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>> variablePositions = new LinkedHashMap<GeneralizedRule, Map<TRSVariable,Set<Pair<FunctionSymbol,Integer>>>>();
        for (GeneralizedRule rule : ruleAnalysis.getRules()) {
            Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>> vPos = new LinkedHashMap<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>();
            this.collectVariables(rule.getLeft(), new ArrayList<Pair<FunctionSymbol, Integer>>(), vPos, ruleAnalysis.getPreDefinedMap());
            this.collectVariables(rule.getRight(), new ArrayList<Pair<FunctionSymbol, Integer>>(), vPos, ruleAnalysis.getPreDefinedMap());
            variablePositions.put(rule, vPos);
        }

        ImmutableSet<FunctionSymbol> fss = ruleAnalysis.getFunctionSymbols();
        Map<FunctionSymbol, boolean[]> usedPositions = new LinkedHashMap<FunctionSymbol, boolean[]>();
        for (FunctionSymbol fs : fss) {
            usedPositions.put(fs, new boolean[fs.getArity()]);
        }

        this.initializeFilter(ruleAnalysis, usedPositions, variablePositions);

        Map<FunctionSymbol, ImmutableCollection<Integer>> res = new LinkedHashMap<FunctionSymbol, ImmutableCollection<Integer>>();
        int countFiltered = 0;
        int countUnfiltered = 0;
        for (Map.Entry<FunctionSymbol, boolean[]> entry : usedPositions.entrySet()) {
            // do not filter pre-defined positions (in fact impossible by def.)
            if (predefinedMap.isPredefined(entry.getKey())) {
                res.put(entry.getKey(), ImmutableCreator.create(Collections.<Integer>emptySet()));
            } else {
                Set<Integer> filtered = new LinkedHashSet<Integer>(entry.getKey().getArity());
                boolean[] used = entry.getValue();
                for (int i = used.length-1; i >=0; i--) {
                    if (!used[i]) {
                        if (Globals.DEBUG_MPLUECKER) {
                            AbstractFilterHeuristic.log.finest("AbstractFilterHeuristic FILTER " + entry.getKey() + "/" + i);
                        }
                        countFiltered ++;
                        filtered.add(i);
                    } else {
                        countUnfiltered++;
                    }
                }
                res.put(entry.getKey(), ImmutableCreator.create(filtered));
            }
        }
        AbstractFilterHeuristic.log.fine("AbstractFilterHeuristic - FILTERED: " + countFiltered + " UNFILTERED: " + countUnfiltered);
        this.cache.put(ruleAnalysis, res);
    }

    protected abstract void initializeFilter(IDPRuleAnalysis ruleAnalysis, Map<FunctionSymbol, boolean[]> usedPositions, Map<GeneralizedRule, Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>> variablePositions);

    protected void activatePosition(
            FunctionSymbol fs,
            int pos,
            Map<FunctionSymbol, boolean[]> usedPositions,
            IDPPredefinedMap predefinedMap,
            ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap,
            Map<GeneralizedRule, Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>> variablePositions) {
        boolean[] used = usedPositions.get(fs);
        if (used[pos]) {
            return;
        }
        used[pos] = true;
        if (!ruleMap.containsKey(fs)) {
            return;
        }
        for (GeneralizedRule rule : ruleMap.get(fs)) {
            Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>> varPos = variablePositions.get(rule);
            for (TRSVariable var : rule.getLeft().getArgument(pos).getVariables()) {
                for (Pair<FunctionSymbol, Integer> newActive : varPos.get(var)) {
                    AbstractFilterHeuristic.log.finest("Activate " + fs + "/" + pos + " -> " + newActive.x + "/" + newActive.y);
                    this.activatePosition(newActive.x, newActive.y, usedPositions, predefinedMap, ruleMap, variablePositions);
                }
            }
        }
    }


    /**
     * Collects all variables except those in non arithmetic pre-defined functions
     */
    protected void collectVariables(TRSTerm t, List<Pair<FunctionSymbol, Integer>> currentPath, Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>> variablePositions, IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            Set<Pair<FunctionSymbol, Integer>> varPos = variablePositions.get(v);
            if (varPos == null) {
                varPos = new LinkedHashSet<Pair<FunctionSymbol,Integer>>();
                variablePositions.put(v, varPos);
            }
            varPos.addAll(currentPath);
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication) t;
            FunctionSymbol fs = fa.getRootSymbol();
            ImmutableList<TRSTerm> arguments = fa.getArguments();
            PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(fs);
            if (func != null) {
                if (!func.isArithmetic() && (this.filterRelations || !func.isRelation())) {
                    return;
                }
            }
            for (int i = arguments.size() -1; i>=0; i--) {
                currentPath.add(new Pair<FunctionSymbol, Integer>(fs, i));
                this.collectVariables(arguments.get(i), currentPath, variablePositions, predefinedMap);
                currentPath.remove(currentPath.size()-1);
            }
        }
    }


    public static class Arguments {
        public boolean filterRelations = true;
    }
}
