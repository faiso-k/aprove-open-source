package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * Edge used in case a refinement was done, but led to a forbidden state (for
 * example by introducing cycles)
 */
public class FailedRefinementEdge extends DebugEdge {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = -7624964225693137942L;

    /**
     * Create an edge used to connect a state with a child created through
     * refinement.
     * @param l label
     */
    public FailedRefinementEdge(final String l) {
        super("failed ref: " + l);
    }
}
