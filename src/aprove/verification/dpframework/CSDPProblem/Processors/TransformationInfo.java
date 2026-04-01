package aprove.verification.dpframework.CSDPProblem.Processors;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class TransformationInfo {
    private final boolean complete;

    private final ImmutableSet<Rule> rules;

    private final boolean reconnectRhs;

    TransformationInfo(boolean complete, boolean reconnectRhs,
            ImmutableSet<Rule> rules) {
        this.reconnectRhs = reconnectRhs;
        this.complete = complete;
        this.rules = rules;
    }

    public boolean isComplete() {
        return this.complete;
    }

    public boolean mustReconnectRhs() {
        return this.reconnectRhs;
    }

    public ImmutableSet<Rule> getRules() {
        return this.rules;
    }

}
