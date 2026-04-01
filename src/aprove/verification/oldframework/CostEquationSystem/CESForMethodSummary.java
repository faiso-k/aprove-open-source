package aprove.verification.oldframework.CostEquationSystem;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.MethodSummaryBuilder.*;

public class CESForMethodSummary extends CostEquationSystem {

    private MethodSummaryBuilder.Task task;
    private Map<Integer, ComplexityGoalTerm> startTermArgMap;

    public CESForMethodSummary(String name, TRSFunctionApplication startTerm, Set<CostEquation> equations,
            Task task,
            Map<Integer, ComplexityGoalTerm> startTermArgMap)
    {
        super(name, startTerm, equations);
        this.task = task;
        this.startTermArgMap = startTermArgMap;
    }

    @Override
    public String export(Export_Util eu) {
        return task + eu.linebreak() + super.export(eu);
    }

    public MethodSummaryBuilder.Task getTask() {
        return task;
    }

    public Map<Integer, ComplexityGoalTerm> getStartTermArgMap() {
        return startTermArgMap;
    }

    @Override
    public CESForMethodSummary copyWithNewRules(Collection<CostEquation> newRules) {
        return new CESForMethodSummary(super.getName(), super.getStartTerm(), new LinkedHashSet<>(newRules), this.task, this.startTermArgMap);
    }

}
