package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.MethodSummaryBuilder.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

public class WeightedIntTrsForMethodSummary extends WeightedIntTrs {

    private MethodSummaryBuilder.Task task;
    private Map<Integer, ComplexityGoalTerm> startTermArgMap;

    public WeightedIntTrsForMethodSummary(Set<WeightedRule> rules, TRSFunctionApplication startTerm, String name,
            Task task,
            Map<Integer, ComplexityGoalTerm> startTermArgMap) {
        super(rules, startTerm, name, ConsideredPaths.ALL_PATHS_FROM_START);
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
    public WeightedIntTrsForMethodSummary copyWithNewRules(Collection<WeightedRule> newRules) {
        return new WeightedIntTrsForMethodSummary(new LinkedHashSet<>(newRules), super.getStartTerm(), super.getName(), this.task, this.startTermArgMap);
    }
}
