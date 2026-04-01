package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * This is a standard evaluation that is added iff we start a new method (add a
 * new stack frame).
 * @author cotto
 */
public class MethodStartEdge extends EvaluationEdge {
    /**
     * Some UID.
     */
    private static final long serialVersionUID = 1682958783377213932L;

    /**
     * True iff this invokation is a tail call.
     */
    private final boolean isTailCall;

    /**
     * Create a new Method Start Edge.
     * @param isTailCallParam true iff this invokation is a tail call.
     */
    public MethodStartEdge(final boolean isTailCallParam) {
        this.isTailCall = isTailCallParam;
    }

    /**
     * Create a new Method Skip Edge.
     */
    public MethodStartEdge() {
        this(false);
    }

    @Override
    public String toString() {
        if (this.isTailCall) {
            return "<<method start (tail call)>>" + super.toString();
        }
        return "<<method start>>" + super.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#FF3300\"";
    }

    /**
     * @return true iff this invokation is a tail call.
     */
    public boolean isTailCall() {
        return this.isTailCall;
    }

}
