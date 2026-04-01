package aprove.api.decisions.impl;

import java.util.*;
import java.util.stream.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;

public class EvaluationStrategyDecisionImpl implements EvaluationStrategyDecision {

    public static EvaluationStrategyDecisionImpl create(EvaluationStrategy defaultEvaluationStrategy,
                                                        List<EvaluationStrategy> evaluationStrategies) {
        return new EvaluationStrategyDecisionImpl(defaultEvaluationStrategy.getName(),
                                                  evaluationStrategies.stream()
                                                                      .map(EvaluationStrategy::getName)
                                                                      .collect(Collectors.toList()));
    }

    private final String defaultEvaluationStrategy;
    private final List<String> evaluationStrategies;

    public EvaluationStrategyDecisionImpl(String defaultEvaluationStrategy,
                                          List<String> evaluationStrategies) {
        this.defaultEvaluationStrategy = defaultEvaluationStrategy;
        this.evaluationStrategies = evaluationStrategies;
    }

    @Override
    public String getDefaultEvaluationStrategy() {
        return defaultEvaluationStrategy;
    }

    @Override
    public List<String> getEvaluationStrategies() {
        return evaluationStrategies;
    }

    public EvaluationStrategyDecisionResult makeDecision(String evaluationStrategy) throws InvalidDecisionException {
        Objects.requireNonNull(evaluationStrategy);
        return EvaluationStrategy.getByName(evaluationStrategy)
                                 .map(es -> new EvaluationStrategyDecisionResult(this, es))
                                 .orElseThrow(() -> new InvalidDecisionException("unknown evaluation strategy: "
                                                                                 + evaluationStrategy));
    }
}
