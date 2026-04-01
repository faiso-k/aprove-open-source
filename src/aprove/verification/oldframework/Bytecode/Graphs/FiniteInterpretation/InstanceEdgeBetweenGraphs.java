package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * After combining the individual method graphs into a single termination graph,
 * this edge is used to connect the node of some abstracted state to the node
 * representing the start node of the (previously existing) method graph of the
 * called method.
 * @author cotto
 */
public class InstanceEdgeBetweenGraphs extends InstanceEdge {
    /**
     * Some UID.
     */
    private static final long serialVersionUID = -1595119244860110185L;

    public InstanceEdgeBetweenGraphs() {
        super("instance, is call abstraction", false);
    }
}
