package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class DefiniteGroupingCriterion implements GroupingCriterion {

    private LowerBoundsToolbox toolbox;
    private Map<Pair<SampleConjectureMap, RewriteSequence>, Boolean> cache = new LinkedHashMap<>();

    public DefiniteGroupingCriterion(LowerBoundsToolbox toolbox) {
        this.toolbox = toolbox;
    }

    @Override
    public boolean fits(SampleConjectureMap map, RewriteSequence conjecture) {
        Pair<SampleConjectureMap, RewriteSequence> key = new Pair<>(map, conjecture);
        Boolean res = this.cache.get(key);
        if (res != null) {
            return res;
        }
        Set<AbstractRule> rules = conjecture.getRules();
        if (!map.rulesEqual(rules)) {
            this.cache.put(key, false);
            return false;
        }
        Set<Position> rhsVariables = new LinkedHashSet<>();
        Set<TRSVariable> resultVars = conjecture.getResult().getVariables();
        for (Entry<TRSVariable, List<Position>> e: conjecture.getLhs().getVariablePositions().entrySet()) {
            if (resultVars.contains(e.getKey())) {
                rhsVariables.addAll(e.getValue());
            }
        }
        if (!map.rhsVariablesEquals(rhsVariables)) {
            this.cache.put(key, false);
            return false;
        }
        TRSTerm t = conjecture.getResultRL();
        TRSTerm newScheme = this.toolbox.pfHelper.abstractFromIntConstants(t);
        if (!map.schemeEquals(newScheme)) {
            this.cache.put(key, false);
            return false;
        }
        this.cache.put(key, true);
        return true;
    }

}
