package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;


/**
 * Edge used when we introduce a new start state to connect the old one to the
 * new one.
 */
public class NewStartStateEdge extends DebugEdge {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = 5160264457372646505L;

    /**
     * Create an edge used to connect the old start state with the new start
     * state.
     * @param nodeNr the node number of the node causing the new start node to
     * exist
     */
    public NewStartStateEdge(final int nodeNr) {
        super("new start state (" + nodeNr + ")");
    }
}
