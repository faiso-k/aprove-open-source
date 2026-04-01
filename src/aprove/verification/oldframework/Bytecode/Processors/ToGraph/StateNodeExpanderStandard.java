package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Worker class used to expand leaves in this method graph
 */
public class StateNodeExpanderStandard extends StateNodeExpander {

    /**
     * Constructs a new worker expanding the node passed as argument.
     * @param node Some (leaf) node in the constructed method graph that should
     * be expanded.
     * @param graph the method graph containing the node
     */
    public StateNodeExpanderStandard(final MethodGraph graph, final Node node) {
        super(graph, node);
    }

    /**
     * Do a standard expansion (evaluation, refinement, ...).
     * @throws AbortionException if the aborter kicks in
     */
    @Override
    protected void executeInternally() throws AbortionException {
        final State currentState = this.getNodeToExpand().getState();
        // get all successors
        Collection<Pair<State, ? extends EdgeInformation>> expandedStates = expand(currentState);
        // handle all successors:
        for (final Pair<State, ? extends EdgeInformation> p : expandedStates) {
            final State newState = p.x;
            final EdgeInformation edge = p.y;

            /*
             * addStateToGraph will return null when it was interrupted
             * (for example because it tried merging with a state which
             * was then deleted). Try to repeat it until we get a result
             * (which will be the empty list if the expanded node itself
             * was removed in the meantime).
             */
            Collection<MethodGraphWorker> result = null;
            while (result == null) {
                result = this.getMethodGraph().addStateToGraph(this.getNodeToExpand(), newState, edge);
            }

            this.getMethodGraph().getTerminationGraph().addJobs(result);
        }
    }

    /**
     * Computes needed successors. This can either be a single evaluation result
     * or a refinement/split successor - which kind of operation was performed
     * is indicated by a edge that is returned together with the state. In case
     * that evaluation is done (i.e. the last stackframe was popped), no
     * successor is returned.
     * @param state the state to expand
     * @return collection of states obtained by expansion
     * @throws AbortionException if this method is aborted
     */
    public static Collection<Pair<State, ? extends EdgeInformation>> expand(final State state) throws AbortionException {
        /*
         * If the callstack is empty, then the program is done and no
         * successor state exists.
         */
        if (state.callStackEmpty()) {
            return Collections.emptySet();
        }

        final Collection<Pair<State, ? extends EdgeInformation>> newStates = new LinkedList<>();

        /*
         * At startup, we need to initialize several classes before we actually
         * start running the program. At the end of this process we need to
         * initialize the current class.
         */
        final Pair<State, InitializationStateChange> updatedInitStatus =
            state.getClassInitInfo().setBaseClassesInitState(state);
        if (updatedInitStatus != null) {
            /*
             * We changed the init status from MAYBE to NO (or directly YES)
             * for some class.
             */
            newStates.add(updatedInitStatus);
            return newStates;
        }

       /*
         * Do we need to start initialization of some class that is
         * marked with an initialization status of NO?
         */
        final Pair<State, InitializationStateChange> performedInit =
            state.getClassInitInfo().initializeNeededClasses(state);
        if (performedInit != null) {
            /*
             * We changed the init status from NO to RUNNING/YES for
             * some class and added <clinit> if needed.
             */
            newStates.add(performedInit);
            return newStates;
        }

       final StackFrame currentFrame = state.getCurrentStackFrame();
        if (currentFrame.hasException()) {
            OpCode.handleException(state, newStates);
        } else {
            final OpCode currentOpCode = currentFrame.getCurrentOpCode();
            // maybe we need to refine information before we can evaluate
            final boolean refined = currentOpCode.refine(state, newStates);
            if (!refined) {
                // no refinement was needed, evaluate
                Pair<State, ? extends EdgeInformation> res = currentOpCode.evaluate(state);
                if (res != null) {
                    newStates.add(res);
                }
            }
        }

       for (final Pair<State, ? extends EdgeInformation> pair : newStates) {
            final Pair<Boolean, Set<VariableInformation>> res = pair.x.gc();
            pair.y.addAll(res.y);
        }

       return newStates;
    }
}
