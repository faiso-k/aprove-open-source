package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;

/**
 * @author marinag
 * Location in the cooperation program
 */
public interface CoopLocation {

    public Location getOriginalLocation();

    public CoopLocationType getType();
}
