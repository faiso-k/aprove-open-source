package aprove.verification.oldframework.Bytecode.Consistency;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * This checker checks for inconsistent outgoing edges in nodes:
 * <ul>
 * <li>An outgoing eval edge means exactly one outgoing edge
 * <li>Same for an outgoing instance edge
 * <li>Same for an outgoing init state change edge
 * <li>One outgoing refinement edge means only refinement edges exist
 * <li>Same for split edges
 * </ul>
 * @author christian
 */
public class OutEdgeTypes implements Checker {
    /**
     * The graph to be checked
     */
    private final MethodGraph graph;

    /**
     * If one node does not pass the test, it is saved here. If there is no such node,
     * or if the test wasn't performed, then this is null
     */
    private Node failNode;

    /**
     * @param g graph to check
     */
    public OutEdgeTypes(final MethodGraph g) {
        this.graph = g;
        this.failNode = null;
    }


    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Consistency.Checker#check()
     */
    @Override
    public boolean check() {
        for (final Node n : this.graph.getNodes()) {
            if (n.getOutEdges().size() > 0) {
                Edge e = n.getOutEdges().iterator().next();

                final EdgeInformation i = e.getLabel();
                if (i instanceof EvaluationEdge || i instanceof InstanceEdge
                    || i instanceof InitializationStateChange) {
                    for (final Edge eo : n.getOutEdges()) {
                        final Node out = eo.getEnd();
                        if (!out.equals(e.getEnd())) {
                            this.failNode = n;
                            return false;
                        }
                    }
                } else if (i instanceof EQRefinementEdge) {
                    int refines = 0;
                    int eqRefines = 0;
                    int nonEqRefines = 0;
                    for (final Edge eo : n.getOutEdges()) {
                        if (eo.getLabel() instanceof RefinementEdge) {
                            refines++;
                            if (eo.getLabel() instanceof EQRefinementEdge) {
                                eqRefines++;
                            } else {
                                nonEqRefines++;
                            }
                            if (refines > 2 || eqRefines > 1
                                || nonEqRefines > 1) {
                                this.failNode = n;
                                return false;
                            }
                        }
                    }
                } else if (i instanceof RefinementEdge) {
                    for (final Edge eo : n.getOutEdges()) {
                        if (!(eo.getLabel() instanceof RefinementEdge) && (!(eo.getLabel() instanceof FailedRefinementEdge))) {
                            this.failNode = n;
                            return false;
                        }
                    }

                } else if (i instanceof SplitEdge) {
                    for (final Edge eo : n.getOutEdges()) {
                        if (!(eo.getLabel() instanceof SplitEdge)) {
                            this.failNode = n;
                            return false;
                        }
                    }
                } else if (i instanceof CallAbstractEdge
                    || i instanceof MethodSkipEdge) {
                    for (final Edge eo : n.getOutEdges()) {
                        if (eo.getLabel() instanceof DebugEdge) {
                            continue;
                        }
                        if (   !(eo.getLabel() instanceof MethodSkipEdge)
                            && !(eo.getLabel() instanceof CallAbstractEdge)) {
                            this.failNode = n;
                            return false;
                        }
                    }

                } else {
                    assert (false) : "This case shouldn't exist, "
                        + i.getClass();
                    return false;
                }
            }
        }
        return true;
    }



    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        if (this.failNode == null) {
            return "Check passed.";
        } else {
            return this.failNode + " has inconsistent outgoing edges";
        }
    }

}
