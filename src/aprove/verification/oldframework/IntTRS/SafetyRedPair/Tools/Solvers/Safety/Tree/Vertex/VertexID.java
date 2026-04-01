package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.Vertex;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;

/**
 * Unwinding tree vertex id
 * @author marinag
 */
public class VertexID {

    /**
     * Unique id
     */
    private final int id;
    private final Location location;
    protected LinearDisjunction labeling = LinearDisjunction.TRUE;

    private VertexID(final int id, final Location l) {
        this.id = id;
        this.location = l;
    }

    public static VertexID create(final int id, final Location l) {
        return new VertexID(id, l);
    }

    /**
     * @return id
     */
    public int getId() {
        return this.id;
    }

    public Location getLocation() {
        return this.location;
    }

    /**
     * @return labeling formula
     */
    public LinearDisjunction getLabeling() {
        return this.labeling;
    }

    public void setLabeling(final LinearDisjunction labeling) {
        this.labeling = labeling;

    }
}
