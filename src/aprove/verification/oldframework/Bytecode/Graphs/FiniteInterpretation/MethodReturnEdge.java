package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * This edge marks the end of a method (from the state having some kind of
 * return to the state following the invocation of the ending method). This must
 * not be used during the graph construction!
 * @author cotto
 */
public class MethodReturnEdge extends DebugEdge {

    /**
     * Some UID.
     */
    private static final long serialVersionUID = 1682958783377213932L;

    @Override
    public String toString() {
        return "<<method return>>" + super.toString();
    }
}
