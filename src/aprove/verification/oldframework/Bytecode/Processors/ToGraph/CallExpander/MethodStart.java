package aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;

/**
 * Deal with a method call. This either does nothing and returns a standard
 * expand job or, if we want to split the termination graph, call abstraction is
 * done.
 */
public class MethodStart extends StateNodeExpander {
    /**
     * Constructs a new worker expanding the node passed as argument.
     * @param node Some (leaf) node in the constructed method graph that should
     * be expanded.
     * @param graph the method graph containing the node
     */
    public MethodStart(final MethodGraph graph, final Node node) {
        super(graph, node);
    }

    /**
     * Deal with a method call. This either does nothing and returns a standard
     * expand job or, if we want to split the termination graph, call
     * abstraction is done.
     * @throws AbortionException if the aborter kicks in
     */
    @Override
    protected void executeInternally() throws AbortionException {
        final MethodGraph mGraph = this.getMethodGraph();
        State newState;
        final Node node = this.getNodeToExpand();
        try {
            mGraph.getGraphLock().readLock().lock();
            final boolean isTailCall = this.isTailCall();

            if (!MethodStart.doSplit(node.getState(), mGraph.getJBCOptions(), isTailCall)) {
                final MethodGraphWorker standardTask = new StateNodeExpanderStandard(mGraph, this.getNodeToExpand());
                mGraph.getTerminationGraph().addJob(standardTask);
                return;
            }

            // nothing to do, outgoing instance edge
            for (final Edge outEdge : node.getOutEdges()) {
                if (outEdge.getLabel() instanceof InstanceEdge) {
                    return;
                }
            }

            newState = node.getState();

            assert (newState.getCallStack().size() >= 2);

            // only retain the top stack frame and create input references

            // we may add a NRIR (for this call) to some existing NRIR
        } finally {
            mGraph.getGraphLock().readLock().unlock();
        }
        final State reducedState;
        boolean acquired = false;
        try {
            acquired = mGraph.getTerminationGraph().acquireAllLocks();
            reducedState = this.getReducedState(newState);
        } finally {
            if (acquired) {
                mGraph.getTerminationGraph().releaseAllLocks();
            }
        }

        // Add the reduced state to the graph
        Collection<MethodGraphWorker> result = null;
        while (result == null) {
            result =
                this.getMethodGraph().addStateToGraph(this.getNodeToExpand(), reducedState, new CallAbstractEdge());
        }

        try {
            mGraph.getGraphLock().readLock().lock();

            if (Globals.useAssertions) {
                if (result.size() == 0) {
                    // nothing to do, outgoing instance edge
                    boolean outgoingInstance = false;
                    for (final Edge outEdge : node.getOutEdges()) {
                        if (outEdge.getLabel() instanceof InstanceEdge) {
                            outgoingInstance = true;
                        }
                    }
                    assert (outgoingInstance || !this.getMethodGraph().containsNode(this.getNodeToExpand()));
                } else {
                    assert (result.size() == 1) : "something might need to be added";
                }
            }

            this.getMethodGraph().getTerminationGraph().addJobs(result);
        } finally {
            mGraph.getGraphLock().readLock().unlock();
        }
    }

    /**
     * @return true if the predecessors indicate that this is a tail call
     */
    private boolean isTailCall() {
        this.getMethodGraph().getGraphLock().readLock().lock();
        // strange code because of https://bugs.eclipse.org/bugs/show_bug.cgi?id=368996
        boolean found = false;
        boolean ret = false;
        try {
            final Node node = this.getNodeToExpand();
            for (final Edge inEdge : node.getInEdges()) {
                if (inEdge.getLabel() instanceof InstanceEdgeMethodStartMerge) {
                    found = true;
                    ret = false;
                    break;
                }
                if (inEdge.getLabel() instanceof MethodStartEdge) {
                    found = true;
                    ret = ((MethodStartEdge) inEdge.getLabel()).isTailCall();
                    break;
                }
            }
            if (!found) {
                assert (!this.getMethodGraph().containsNode(node));
            }
        } finally {
            this.getMethodGraph().getGraphLock().readLock().unlock();
        }
        return ret;
    }

    /**
     * @return true iff we want to split this method call
     * @param newState the state to expand
     * @param jbcOptions the JBC options
     * @param isTailCall true if this is a tail call
     */
    public static boolean doSplit(final State newState, final JBCOptions jbcOptions, final boolean isTailCall) {
        assert (newState.getCurrentOpCode().getPos() == 0);
        final IMethod currentMethod = newState.getCurrentOpCode().getMethod();
        final StackFrame prevFrame = newState.getCallStack().get(1);
        final HandlingMode handlingMode = newState.getTerminationGraph().getGoal();

        return !isTailCall && MethodStart.shouldSplitMethodAnalysis(prevFrame, currentMethod, jbcOptions, handlingMode);
    }

    /**
     * @param newState the state to reduce to the top stack frame
     * @return a reduced state that only has the top stack frame of this state
     * (and input references and only the relevant static fields)
     */
    private State getReducedState(final State newState) {
        final State reducedState = newState.clone();
        reducedState.getCallStack().abstractToTopStackFrame();
        reducedState.getInputReferences().addReferencesForMethodCall(newState, this.getMethodGraph());
        reducedState.gc();
        return reducedState;
    }

    /**
     * When invoking a method, we can analyze the invoked method in a separate
     * MethodGraph, or we can inline the code. This method uses strange
     * heuristics to decide what we want to do.
     * @param invokingFrame the stackframe invoking the method (we use it to
     * extract the invoking method and the exact invoking bytecode).
     * @param invokedMethod the method being invoked by invokingMethod
     * @param jbcOptions the JBC options
     * @return false iff the invoked method should be analyzed using inlining
     */
    public static boolean shouldSplitMethodAnalysis(
        final StackFrame invokingFrame,
        final IMethod invokedMethod,
        final JBCOptions jbcOptions,
        final HandlingMode handlingMode)
    {
        final IMethod invokingMethod = invokingFrame.getMethod();
        final OpCode invokingInstr = invokingFrame.getCurrentOpCode();

        final MethodIdentifier invokedMID = invokedMethod.getMethodIdentifier();

        if (invokedMID.getMethodName().contains("COTTO_SPLITME")) {
            return true;
        }

        if (!jbcOptions.trySeparateMethodAnalysis) {
            return false;
        }

        //Always split calls to equals and hashCode:
        if (invokedMID.getMethodName().equals("equals")
            && invokedMID.getDescriptor().getArgumentCount() == 1
            && invokedMID.getDescriptor().getType(0).equals(FuzzyClassType.FT_JAVA_LANG_OBJECT)
            && invokedMethod.getStart().getNextOp() != null)
        {
            return true;
        }
        if (invokedMID.getMethodName().equals("hashCode") && invokedMID.getDescriptor().getArgumentCount() == 0) {
            return true;
        }

        boolean result = false;

        final int curLoops = invokingMethod.getNumberOfLoops();
        final int newLoops = invokedMethod.getNumberOfLoops();
        final int curBranches = invokingMethod.getNumberOfBranches();
        final int newBranches = invokedMethod.getNumberOfBranches();
        final int curCalls = invokingMethod.getNumberOfMethodCalls();
        final int newCalls = invokedMethod.getNumberOfMethodCalls();
        final int curCallsInLoops = invokingMethod.getNumberOfCallsInLoops();
        final int newCallsInLoops = invokedMethod.getNumberOfCallsInLoops();
        final int curCallsToThatMethod = invokingMethod.getNumberOfMethodCalls(invokedMethod.getMethodIdentifier());
        final boolean curIsRecursive = invokingMethod.isRecursive();
        final boolean newIsRecursive = invokedMethod.isRecursive();
        final boolean usesRandom = invokedMethod.usesRandom();
        final boolean writesObjects = invokedMethod.writesObjects();
        final boolean readsObjects = invokedMethod.readsObjects();
        final boolean newHasIntLoop = invokedMethod.hasIntLoop();
        final boolean callIsInLoop = invokingMethod.isInLoop(invokingInstr.getPos());

        if (handlingMode != HandlingMode.Termination) {
            return newIsRecursive; //for now we want to avoid splitting in complexity analysis
        }

        //Always split iff the new method is recursive:
        if (newIsRecursive) {
            result = true;
        } else if (usesRandom) {
            result = true;
        } else {
            /*
             * Split possibly looping methods from a method that already has
             * loops and calls a lot of methods:
             */
            if (curLoops > 1 && curCalls >= 5 && newHasIntLoop) {
                result = true;
                /*
                 * For object-handling methods, we will probably go to QDP.
                 * However, if inlining the method would just result in another
                 * wrapped int loop without side effects, we can also profit from
                 * a split in IDP:
                 */
            } else if (!readsObjects && !writesObjects && !newHasIntLoop && newBranches >= 4) {
                result = true;
            } else if (!newHasIntLoop || (curIsRecursive && newHasIntLoop && !writesObjects)) {
                if (callIsInLoop || newBranches >= 2) {
                    result = newLoops >= 1;
                } else if (curCallsToThatMethod > 5) {
                    result = true;
                } else {
                    result = newLoops > 1;
                }
            } else if (writesObjects) {
                result = (curLoops > 0) && (curLoops + curBranches + newLoops + newBranches >= 3);
            } else if (callIsInLoop && !readsObjects && !writesObjects && (curCallsInLoops + newCallsInLoops) >= 2) {
                result = true;
            } else {
                //For others, we will probably stay in IDP, thus split late:
                result = (curLoops + curBranches + newLoops + newBranches >= 10);
            }
        }
        if (Globals.DEBUG_MARC) {
            final String curMethodName = invokingMethod.toString();
            final String newMethodName = invokedMethod.toString();
            if (result) {
                System.out.print("Splitting ");
            } else {
                System.out.print("Not splitting ");
            }
            System.out.println("call from "
                + curMethodName
                + " to "
                + newMethodName
                + (newIsRecursive ? " (recursive) " : "")
                + (usesRandom ? " (uses random) " : "")
                + (writesObjects ? " (writes objs) " : "")
                + (readsObjects ? " (reads objs) " : "")
                + (newHasIntLoop ? " (has int loop) " : "")
                + "(curLoops: "
                + curLoops
                + ","
                + " newLoops: "
                + newLoops
                + ","
                + " curCalls: "
                + curCalls
                + ","
                + " newCalls: "
                + newCalls
                + ","
                + " curCallsInLoops: "
                + curCallsInLoops
                + ","
                + " newCallsInLoops: "
                + newCallsInLoops
                + ","
                + " curBranch: "
                + curBranches
                + ","
                + " newBranch: "
                + newBranches
                + ")");
        }
        return result;
    }

}
