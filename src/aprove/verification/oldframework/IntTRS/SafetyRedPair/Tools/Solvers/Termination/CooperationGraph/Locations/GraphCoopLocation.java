package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author marinag
 *
 */
public class GraphCoopLocation extends Location implements CoopLocation {
    private final CoopLocationType type;
    private final Location originalLocation;


    public GraphCoopLocation(final Location originalLocation, final CoopLocationType type) {
        super(originalLocation.getId() * 10 + type.ordinal());
        this.type = type;
        this.originalLocation = originalLocation;
    }



    @Override
    public Location getOriginalLocation() {
        return this.originalLocation;
    }

    @Override
    public CoopLocationType getType() {
        return this.type;
    }

    @Override
    public String prettyToString() {
        return this.type.toString() + String.valueOf(this.originalLocation.getId());
    }

    @Override
    public int compareTo(final Node<?> node) {
        if (this.equals(node)) {
            return 0;
        }

        assert node instanceof CoopLocation;
        final CoopLocation l = (CoopLocation) node;

        if (this.getType().equals(l.getType())) {
            this.originalLocation.compareTo(l.getOriginalLocation());
        }

        return (this.getType().equals(CoopLocationType.SAFETY)) ? 1 : -1;
    }


}
