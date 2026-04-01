package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Implementations provide a simple way to receive all final states at a certain
 * time and in addition receive updates as the final states are changed.
 * @author Fabian K&uuml;rten
 */
public interface MethodEndNotifier {

    /**
     * Upon calling, the currently known end states will be returned.<br/>
     * All new end states will be announced by calls to
     * <code>l.newMethodEnd</code>.<br/>
     * All hidden/deleted method ends will be announced by
     * <code>l.deletedMethodEnd</code>.
     * @param l the listener
     * @return set of (undeleted) final states in this method graph.
     * @see MethodEndListener#newMethodEnd(MethodGraph, State)
     * @see MethodEndListener#deletedMethodEnd(MethodGraph, State)
     */
    Set<State> addMethodEndListener(MethodEndListener l);
}
