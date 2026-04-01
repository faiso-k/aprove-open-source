package aprove.api.decisions.results;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;

public class EvaluationStrategyDecisionResult {

    private final EvaluationStrategyDecision decision;
    private final EvaluationStrategy evaluationStrategy;

    public EvaluationStrategyDecisionResult(EvaluationStrategyDecision decision,
                                            EvaluationStrategy evaluationStrategy) {
        this.decision = decision;
        this.evaluationStrategy = evaluationStrategy;
    }

    public EvaluationStrategyDecision getDecision() {
        return decision;
    }

    public EvaluationStrategy getEvaluationStrategy() {
        return evaluationStrategy;
    }
}
