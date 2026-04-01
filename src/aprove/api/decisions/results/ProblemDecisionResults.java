package aprove.api.decisions.results;

import java.util.*;

import aprove.api.decisions.impl.*;

public class ProblemDecisionResults {

    private final Optional<HandlingModeDecisionResult> handlingMode;
    private final Optional<EvaluationStrategyDecisionResult> evaluationStrategy;
    private final Optional<SymbolDecisionResult> symbol;
    private final Optional<SymbolModingDecisionResult> symbolModing;
    private final Optional<QueryDecisionResult> query;

    public ProblemDecisionResults(Optional<HandlingModeDecisionResult> handlingMode,
                                  Optional<EvaluationStrategyDecisionResult> evaluationStrategy,
                                  Optional<SymbolDecisionResult> symbol,
                                  Optional<SymbolModingDecisionResult> symbolModing,
                                  Optional<QueryDecisionResult> query) {
        this.handlingMode = handlingMode;
        this.evaluationStrategy = evaluationStrategy;
        this.symbol = symbol;
        this.symbolModing = symbolModing;
        this.query = query;
    }

    public HandlingMode getHandlingMode() {
        return handlingMode.get().getHandlingMode();
    }

    public EvaluationStrategy getEvaluationStrategy() {
        return evaluationStrategy.get().getEvaluationStrategy();
    }

    public String getSymbol() {
        return symbol.get().getSymbol();
    }

    public List<Boolean> getSymbolModing() {
        return symbolModing.get().getModing();
    }

    public String getQuery() {
        return query.get().getQuery();
    }
}
