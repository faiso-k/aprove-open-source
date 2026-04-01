package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations.*;

/**
 * @author marinag
 * Creates location for the cooperation program
 */
public abstract class LocationCreator {
    public static Location safetyCopy(final Location l) {
        return new GraphCoopLocation(l, CoopLocationType.SAFETY);
    }

    public static Location termCopy(final Location l) {
        return new GraphCoopLocation(l, CoopLocationType.TERMINATION);
    }

    public static Location cutPoint(final Location l) {
        return new GraphCoopLocation(l, CoopLocationType.CUTPOINT_DUPLICATE);
    }

    public static Location abortLocation(final Location l) {
        return new AbortCoopLocation(l);
    }
}
