package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author marinag
 * Error location in the cooperation propgram
 */
public class AbortCoopLocation extends AbortLocation implements CoopLocation {
    private final Location originalLocation;

    public AbortCoopLocation(final Location originalLocation) {
        super(CoopLocationType.ERROR.createId(originalLocation));
        this.originalLocation = originalLocation;
    }

    @Override
    public Location getOriginalLocation() {
        return this.originalLocation;
    }

    @Override
    public CoopLocationType getType() {
        return CoopLocationType.ERROR;
    }

    @Override
    public String prettyToString() {
        return CoopLocationType.ERROR.toString() + String.valueOf(this.originalLocation.getId());
    }


    @Override
    public int compareTo(final Node<?> node) {
        if (this.equals(node)) {
            return 0;
        }

        assert node instanceof CoopLocation;
        final CoopLocation l = (CoopLocation) node;

        if (this.getType().equals(l.getType()) || (l.getType().equals(CoopLocationType.ERROR))) {
            this.originalLocation.compareTo(l.getOriginalLocation());
        }

        return -1;
    }

}
