package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.Vertex;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Basic vertex of the unwinding tree, for identification
 * @author marinag
 */
public abstract class BasicVertex extends Node<VertexID> {

    /**
     * The edge from the father node father of the corresponding location node in the program graph
     * null in case of a root vertex
     */
    protected final Edge<LinearTransitionPair, LocationID> edge;

    /**
     * Root vertex constructor
     * @param id unique id
     * @param l corresponding location node in the program graph
     */
    public BasicVertex(final int id, final Location l) {
        super(VertexID.create(id, l));
        this.edge = new Edge<>(null, l);
    }

    /**
     * @param id unique id
     * @param t The edge from the father node father of the corresponding location node in the program graph
     */
    public BasicVertex(final int id, final Edge<LinearTransitionPair, LocationID> t) {
        super(VertexID.create(id, (Location) t.getEndNode()));
        this.edge = t;
    }

    public Edge<LinearTransitionPair, LocationID> getProgramEdge() {
        return this.edge;
    }

    /**
     * @return the underlying original location node of the program graph
     */
    public Location getLocation() {
        return (Location) (this.getProgramEdge().getEndNode());
    }

    /**
     * @return unque id
     */
    public int getId() {
        return this.getObject().getId();
    }
}
