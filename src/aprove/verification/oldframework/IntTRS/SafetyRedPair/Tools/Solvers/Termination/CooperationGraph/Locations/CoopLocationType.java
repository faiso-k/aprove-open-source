package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;

public enum CoopLocationType {
    SAFETY("S"),
    TERMINATION("T"),
    CUTPOINT_DUPLICATE("D"),
    ERROR("E");

    String token;

    private CoopLocationType(final String token) {
        this.token = token;
    }

    @Override
    public String toString() {
        return this.token;

    }

    public boolean isTermination() {
        return this == CoopLocationType.TERMINATION || this == CoopLocationType.CUTPOINT_DUPLICATE
            || this == CoopLocationType.ERROR;
    }

    public boolean isSafety() {
        return this == CoopLocationType.SAFETY;
    }

    public int createId(final Location originalLocation) {
        return this.ordinal() + originalLocation.getId() * 10;
    }


}