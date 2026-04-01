package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations;


import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author marinag
 * Cut point duplication location
 */
public class CutPointDupLocation extends Location implements CoopLocation {
    private final Location originalLocation;
    private final LinLexRanking rf;

    /**
     * @param originalLocation
     * @param postfix
     * @param aborter
     */
    public CutPointDupLocation(
        final Location originalLocation,
        final String postfix,
        final Abortion aborter)
    {
        super(CoopLocationType.CUTPOINT_DUPLICATE.createId(originalLocation));
        this.originalLocation = originalLocation;
        this.rf = new LinLexRanking(postfix, aborter);
    }


    public LinLexRanking getRanking() {
        return this.rf;
    }

    @Override
    public Location getOriginalLocation() {
        return this.originalLocation;
    }

    @Override
    public CoopLocationType getType() {
        return CoopLocationType.CUTPOINT_DUPLICATE;
    }

    @Override
    public String prettyToString() {
        return CoopLocationType.CUTPOINT_DUPLICATE.toString() + String.valueOf(this.originalLocation.getId());
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

        return (l.getType().equals(CoopLocationType.ERROR)) ? 1 : -1;
    }

}
