package aprove.api.decisions.results;

import aprove.api.decisions.*;

public class SymbolDecisionResult {

    private final SymbolDecision decision;
    private final String symbol;

    public SymbolDecisionResult(SymbolDecision decision, String symbol) {
        this.decision = decision;
        this.symbol = symbol;
    }

    public SymbolDecision getDecision() {
        return decision;
    }

    public String getSymbol() {
        return symbol;
    }
}
