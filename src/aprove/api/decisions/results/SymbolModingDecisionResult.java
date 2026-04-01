package aprove.api.decisions.results;

import java.util.*;

import aprove.api.decisions.*;

public class SymbolModingDecisionResult {

    private final SymbolModingDecision decision;
    private final List<Boolean> moding;

    public SymbolModingDecisionResult(SymbolModingDecision decision, List<Boolean> moding) {
        this.decision = decision;
        this.moding = moding;
    }

    public SymbolModingDecision getDecision() {
        return decision;
    }

    public List<Boolean> getModing() {
        return moding;
    }
}
