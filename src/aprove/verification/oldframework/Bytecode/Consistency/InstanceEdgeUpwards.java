package aprove.verification.oldframework.Bytecode.Consistency;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * @author christian
 *
 * This checker assert that there is no instance edge to a node which has an
 * incoming refine or split edge
 */
public class InstanceEdgeUpwards implements Checker {
    /**
     * Graph to check
     */
    private final MethodGraph graph;

    /**
     * If check was called, and an inconsistent instance edge (see class comment),
     * then this is set to such an edge. Otherwise, this is null,
     */
    private Edge malEdge;


    /**
     * @param g The graph to check
     */
    public InstanceEdgeUpwards(final MethodGraph g) {
        this.graph = g;
        this.malEdge = null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Consistency.Checker#check()
     */
    @Override
    public boolean check() {
        this.graph.getGraphLock().readLock().lock();
        try {
            for (final Edge e : this.graph.getEdges()) {
                if (e.getLabel() instanceof InstanceEdge) {
                    for (final Edge in : e.getEnd().getInEdges()) {
                        if (in.getLabel() instanceof RefinementOrSplitEdge) {
                            this.malEdge = e;
                            return false;
                        }
                    }
                }
            }
            return true;
        } finally {
            this.graph.getGraphLock().readLock().unlock();
        }
    }

    @Override
    public String toString() {
        if (this.malEdge != null) {
            return this.malEdge + " is pointing to a node which has an incoming refine or split edge";
        }
        return "Check succeeded.";
    }

}
