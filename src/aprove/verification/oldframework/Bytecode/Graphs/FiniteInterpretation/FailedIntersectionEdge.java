package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;


/**
 * Edge used in case an intersection was attempted, but the result is empty.
 */
public class FailedIntersectionEdge extends DebugEdge {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = 3065177803474041693L;

    /**
     * The returning Node that caused this intersection.
     */
    private final Node returnNode;

    /**
     * Create an edge used to connect a Node with a child created through
     * intersection.
     * @param l label
     * @param returnNodeParam the returning Node that caused this intersection.
     */
    public FailedIntersectionEdge(final String l, final Node returnNodeParam) {
        super(l + " (from node " + returnNodeParam.getNodeNumber() + ")");
        this.returnNode = returnNodeParam;
    }

    /**
     * @return the Node that caused this intersection
     */
    public Node getReturnNode() {
        return this.returnNode;
    }
}
