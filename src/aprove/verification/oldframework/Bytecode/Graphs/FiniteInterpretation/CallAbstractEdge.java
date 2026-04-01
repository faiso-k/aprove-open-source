package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;


/**
 * This is a standard evaluation that is added iff we remove all but the top stackframe.
 * This is an intra methodgraph edge.
 * @author Fabian K&uuml;rten
 */
public class CallAbstractEdge extends EdgeInformation {
    /**
     * Some UID.
     */
    private static final long serialVersionUID = -8641643162565092732L;

    @Override
    public String toString() {
        return "<<call abstract>>" + super.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#00ffff\"";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean showFilled() {
        return true;
    }
}
