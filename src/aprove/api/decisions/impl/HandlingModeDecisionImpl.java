package aprove.api.decisions.impl;

import java.util.*;
import java.util.stream.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;

public class HandlingModeDecisionImpl implements HandlingModeDecision {

    public static HandlingModeDecisionImpl create(HandlingMode defaultHandlingMode, Set<HandlingMode> handlingModes) {
        return new HandlingModeDecisionImpl(defaultHandlingMode.getName(),
                                            handlingModes.stream()
                                                         .map(HandlingMode::getName)
                                                         .collect(Collectors.toList()));
    }

    private final String defaultHandlingMode;
    private final List<String> handlingModes;

    public HandlingModeDecisionImpl(String defaultHandlingMode, List<String> handlingModes) {
        this.defaultHandlingMode = defaultHandlingMode;
        this.handlingModes = handlingModes;
    }

    @Override
    public String getDefaultHandlingMode() {
        return defaultHandlingMode;
    }

    @Override
    public List<String> getHandlingModes() {
        return handlingModes;
    }

    public HandlingModeDecisionResult makeDecision(String handlingMode) throws InvalidDecisionException {
        Objects.requireNonNull(handlingMode);
        return HandlingMode.getByName(handlingMode)
                           .map(hm -> new HandlingModeDecisionResult(this, hm))
                           .orElseThrow(() -> new InvalidDecisionException("unknown handling mode: " + handlingMode));
    }
}
