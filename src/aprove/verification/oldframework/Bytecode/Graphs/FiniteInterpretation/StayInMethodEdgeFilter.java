/**
 *
 */
package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This Edge Filter filter rejects edges when they are not from the same method.
 * A typical usecase is when you only want to find edges up to the point where the current stackframe is left.
 * Note that entering another method that is called from within the current method is okay, this only rejects when the current stackframe is left
 *
 * @author thies
 */
public class StayInMethodEdgeFilter implements EdgeFilter {

    private IMethod method;
    private int stackFrameDistanceFromBottom;
    private boolean workOnFromState;

    /**
     * Creates a filter that will not leave the given method at given stack height
     * @param method the method that we want to stay in
     * @param stackFrameDistanceFromBottom position of the stackframe relative to bottom of callstack, starting at 1 (and not 0!!!)
     * @param workOnFromState whether the filter should by applied to the to or the from state of the Edge
     */
    public StayInMethodEdgeFilter(IMethod method, int stackFrameDistanceFromBottom, boolean workOnFromState) {
        super();
        this.method = method;
        this.stackFrameDistanceFromBottom = stackFrameDistanceFromBottom;
        this.workOnFromState = workOnFromState;
    }

    /**
     * Will create a filter which will not leave the current method of the given state
     * @param state the state from which to extract method information from
     * @param workOnFromState whether the filter should by applied to the to or the from state of the Edge
     */
    public StayInMethodEdgeFilter(State state, boolean workOnFromState) {
        this(state.getCurrentStackFrame().getMethod(), state.getCallStack().size(), workOnFromState);
    }

    @Override
    public boolean selectEdge(Node from, Node to, EdgeInformation edge) {
        try {
            if (workOnFromState) {
                return from.getState().getCallStack().getFromBottom(stackFrameDistanceFromBottom).getMethod().equals(method);
            } else {
                return to.getState().getCallStack().getFromBottom(stackFrameDistanceFromBottom).getMethod().equals(method);
            }
        } catch (IndexOutOfBoundsException e) {
            //the stackframe did not exist
            return false;
        }
    }

}
