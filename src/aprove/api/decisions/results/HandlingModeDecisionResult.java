package aprove.api.decisions.results;

import aprove.api.decisions.*;
import aprove.api.decisions.impl.*;

public class HandlingModeDecisionResult {

    private final HandlingModeDecision decision;
    private final HandlingMode handlingMode;

    public HandlingModeDecisionResult(HandlingModeDecision decision, HandlingMode handlingMode) {
        this.decision = decision;
        this.handlingMode = handlingMode;
    }

    public HandlingModeDecision getDecision() {
        return decision;
    }

    public HandlingMode getHandlingMode() {
        return handlingMode;
    }
}
