package aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * For a state resulting out of a method call (where some preprocessing on this
 * state might be done already) find or create a suitable method graph and
 * connect to it. If the input references do not match yet, we modify the two
 * involved states until we can finally merge (the details are implemented in
 * the method handleIRs()).
 */
public class ConnectToMethodGraph extends StateNodeExpander {
    /**
     * The termination graph.
     */
    private final TerminationGraph tg;

    /**
     * @param node Some (leaf) node in the constructed method graph that should
     * be expanded.
     * @param graph the method graph containing the node
     */
    public ConnectToMethodGraph(final MethodGraph graph, final Node node) {
        super(graph, node);
        this.tg = graph.getTerminationGraph();
    }

    /**
     * Find or create a method graph corresponding to the call and connect to it.
     * @throws AbortionException if the aborter kicks in
     */
    @Override
    protected void executeInternally() throws AbortionException {
        final Collection<MethodGraphWorker> resultingWorkers = new LinkedHashSet<>();
        boolean acquired = false;
        try {
            acquired = this.tg.acquireAllLocks();

            /*
             * Find MethodGraphs that might be usable when disregarding input references. This for example checks for
             * compatible class initialization information.
             */

            // first find a graph that can be used directly (because no input references need to be regarded)
            final Pair<MethodGraph, JBCMergeResult> pair = this.findUsableMethodGraph();
            if (pair != null) {
                final MethodGraph existingMethodGraph = pair.x;
                final JBCMergeResult mergeResult = pair.y;
                resultingWorkers.addAll(this.connectWithExisting(existingMethodGraph, mergeResult, null));
            } else {

                /*
                 * Identify the graphs that might be good to connect to (because the "shape" fits"), maybe after dealing
                 * with input references.
                 */
                final Collection<MethodGraph> existingMethodGraphs = this.findCandidates();

                boolean done = false;
                for (final MethodGraph existingMethodGraph : existingMethodGraphs) {

                    final Result result = this.handleIRs(existingMethodGraph);
                    if (result == Result.FAIL) {
                        continue;
                    } else if (result == Result.JUST_MERGE) {
                        Double maxCost;
                        if (existingMethodGraph.isFinished()) {
                            maxCost = 0.0d;
                        } else {
                            maxCost = null;
                        }
                        final JBCMerger merger = new PathMerger(this.getNodeToExpand().getState(), maxCost);
                        final boolean merged = merger.merge(existingMethodGraph.getStartNode().getState());
                        assert (merged || existingMethodGraph.isFinished());
                        if (!merged) {
                            continue;
                        }
                        final JBCMergeResult mergeResult = merger.getResult();
                        resultingWorkers.addAll(this.connectWithExisting(existingMethodGraph, mergeResult, null));
                        done = true;
                        break;
                    } else if (result.newCallStateThenMerge()) {
                        final State thisClone = result.getThisClone();
                        Double maxCost;
                        if (existingMethodGraph.isFinished()) {
                            maxCost = 0.0d;
                        } else {
                            maxCost = null;
                        }
                        final JBCMerger merger = new PathMerger(thisClone, maxCost);
                        final boolean merged = merger.merge(existingMethodGraph.getStartNode().getState());
                        assert (merged || existingMethodGraph.isFinished());
                        if (!merged) {
                            continue;
                        }
                        final JBCMergeResult mergeResult = merger.getResult();
                        if (thisClone != this.getNodeToExpand().getState()) {
                            resultingWorkers.add(new StateAdder(
                                this.getMethodGraph(),
                                this.getNodeToExpand(),
                                thisClone,
                                new InstanceEdgeInputReferenceChanges(result.getDebugString(), false)));
                        }
                        resultingWorkers.addAll(this.connectWithExisting(existingMethodGraph, mergeResult, null));
                        done = true;
                        break;
                    } else if (result.newCallStateNewStartStateThenMerge()) {
                        final State thisClone = result.getThisClone();
                        final State thatClone = result.getThatClone();
                        final JBCMerger merger = new PathMerger(thisClone, null);
                        final boolean merged = merger.merge(thatClone);
                        assert (merged);
                        final JBCMergeResult mergeResult = merger.getResult();
                        if (thisClone != this.getNodeToExpand().getState()) {
                            resultingWorkers.add(new StateAdder(
                                this.getMethodGraph(),
                                this.getNodeToExpand(),
                                thisClone,
                                new InstanceEdgeInputReferenceChanges(result.getDebugString(), false)));
                        }
                        resultingWorkers.addAll(this.connectWithExisting(existingMethodGraph, mergeResult, thatClone));
                        done = true;
                        break;
                    } else {
                        throw new IllegalStateException();
                    }

                }
                if (!done) {
                    // create a new graph
                    resultingWorkers.add(this.createNewGraph());
                }
            }
            this.getMethodGraph().getTerminationGraph().addJobs(resultingWorkers);
        } finally {
            if (acquired) {
                this.tg.releaseAllLocks();
            }
        }
    }

    /**
     * Create a new method graph and start working on that.
     * @return some expander for the new start state
     */
    private MethodGraphWorker createNewGraph() {
        /*
         * We cannot merge with any existing state, instead create a new
         * MethodGraph based on the current state
         */
        // Create a new graph
        final State startState = this.getNodeToExpand().getState().clone();
        startState.initializeDeletionListeners();
        final MethodGraph newGraph = MethodGraph.create(startState, this.tg);

        // Add the graph
        final IMethod invokedMethod = this.getNodeToExpand().getState().getCurrentStackFrame().getMethod();
        // Add a listener to the new graph
        final Node callAbstractNode = this.findCallAbstractNode();
        if (callAbstractNode == null) {
            return null;
        }

        this.tg.addMethodGraph(invokedMethod, newGraph);

        final Set<State> existingEnds =
            newGraph.addMethodEndListener(this.getMethodGraph().createListener(callAbstractNode));

        // There should not be any existingEnds
        assert (existingEnds.size() == 0);

        // expand the new start state
        return new StateNodeExpanderStandard(newGraph, newGraph.getStartNode());
    }

    /**
     * In case we do not have any input references, try to find a method graph we can directly connect to.
     * @return the method graph we can connect to using the returned merge result or null if no such graph can be found
     */
    private Pair<MethodGraph, JBCMergeResult> findUsableMethodGraph() {
        final State state = this.getNodeToExpand().getState();
        final State mergeWith = state;
        if (!state.getInputReferences().getRootInputReferences().isEmpty()
            || !state.getInputReferences().getNonRootInputReferences().isEmpty())
        {
            return null;
        }

        final IMethod invokedMethod = this.getNodeToExpand().getState().getCurrentStackFrame().getMethod();
        for (final MethodGraph candidate : this.tg.getMethodGraphMap().getNotNull(invokedMethod)) {
            Double maxCost;
            if (candidate.isFinished()) {
                maxCost = 0.0d;
            } else {
                maxCost = null;
            }
            final State start = candidate.getStartNode().getState();
            if (!start.getInputReferences().getRootInputReferences().isEmpty()
                || !start.getInputReferences().getNonRootInputReferences().isEmpty())
            {
                continue;
            }
            final JBCMerger merger = new PathMerger(mergeWith, maxCost);
            if (merger.merge(start)) {
                return new Pair<>(candidate, merger.getResult());
            }
        }
        return null;
    }

    /**
     * For each method, we may have several method graphs. This is needed because of changes in initialized classes etc.
     * By removing all IRs we can check if a method graph is a suitable candidate. This method finds the graphs that we
     * may connect to if the input references also are no problem (or these problems are solved).
     * @return method graphs we should try to connect to (by dealing with the input references). For each method graph
     * it is also returned how much the merge costs, so that we can pick the most fitting graph.
     */
    private Collection<MethodGraph> findCandidates() {
        final Collection<Pair<MethodGraph, Double>> graphs = new LinkedHashSet<>();

        final State state = this.getNodeToExpand().getState();
        final State cleared = state.clone();
        cleared.getInputReferences().getNonRootInputReferences().clear();
        cleared.getInputReferences().getRootInputReferences().clear();
        cleared.gc();

        final IMethod invokedMethod = this.getNodeToExpand().getState().getCurrentStackFrame().getMethod();
        for (final MethodGraph candidate : this.tg.getMethodGraphMap().getNotNull(invokedMethod)) {
            Double maxCost;
            if (candidate.isFinished()) {
                maxCost = 0.0d;
            } else {
                maxCost = null;
            }
            final JBCMerger merger = new PathMerger(cleared, maxCost);
            final State start = candidate.getStartNode().getState();
            final State startMerge;
            startMerge = start.clone();
            startMerge.getInputReferences().getNonRootInputReferences().clear();
            startMerge.getInputReferences().getRootInputReferences().clear();
            startMerge.gc();
            if (merger.merge(startMerge)) {
                graphs.add(new Pair<>(candidate, merger.getResult().getCost()));
            }
        }

        // sort
        final double[] doubleArr = new double[graphs.size()];
        int i = 0;
        for (final Pair<?, Double> pair : graphs) {
            doubleArr[i] = pair.y;
            i++;
        }

        Arrays.sort(doubleArr);

        final Collection<MethodGraph> res = new LinkedList<>();
        OUTER: for (final double doubleValue : doubleArr) {
            for (final Pair<MethodGraph, Double> graphPair : graphs) {
                if (doubleValue == graphPair.y) {
                    res.add(graphPair.x);
                    graphs.remove(graphPair);
                    continue OUTER;
                }
            }
        }
        return res;
    }

    /**
     * Connects to some existing method graph or creates a new start state based
     * on the merge result. The input references are already taken care of!
     * @param existingMethodGraph the graph to merge with
     * @param mergeResult the merge result
     * @param newStartState if not null, this is a new start state used in the merge. Add it to the graph (and expand
     * it) if the merge result indicates an instance.
     * @return the jobs that need to be done (can be empty in case of an
     * instance edge)
     */
    private Collection<MethodGraphWorker> connectWithExisting(
        final MethodGraph existingMethodGraph,
        final JBCMergeResult mergeResult,
        final State newStartState)
    {
        final Collection<MethodGraphWorker> result = new LinkedHashSet<>();
        final Node callAbstractNode = this.findCallAbstractNode();
        assert (callAbstractNode != null);

        final State partnerState = mergeResult.getPartnerState();

        if (mergeResult.partnerEqualsMergedState() && newStartState == null) {
            // we can connect to the existing start state

            final Collection<MethodGraphWorker> newTasks = new LinkedList<>();
            final Node partnerNode = existingMethodGraph.getNode(partnerState);
            if (existingMethodGraph.getJBCOptions().tryNontermProofs()) {
                if (NonTermWorker.numberOfStartedWorkers < NonTermWorker.MAX) {
                    if (existingMethodGraph.getJBCOptions().tryLoopingNontermProofs()) {
                        LoopingNonTermWitnessFinder.runNow(existingMethodGraph, partnerNode, partnerNode, result);
                        NonTermWorker.numberOfStartedWorkers++;
                    }
                    if (existingMethodGraph.getJBCOptions().tryNonLoopingNontermProofs()) {
                        NonLoopingNonTermWitnessFinder.runNow(existingMethodGraph, partnerNode, partnerNode, result);
                        NonTermWorker.numberOfStartedWorkers++;
                    }
                } else {
                    if (existingMethodGraph.getJBCOptions().tryLoopingNontermProofs()) {
                        LoopingNonTermWitnessFinder.runWhenFinished(existingMethodGraph, partnerNode, partnerNode);
                    }
                    if (existingMethodGraph.getJBCOptions().tryNonLoopingNontermProofs()) {
                        NonLoopingNonTermWitnessFinder.runWhenFinished(existingMethodGraph, partnerNode, partnerNode);
                    }
                }
            }

            /*
             * The already existing method graph can be used for the current
             * call. We just add a listener to the graph.
             */
            final Set<State> existingEnds =
                existingMethodGraph.addMethodEndListener(this.getMethodGraph().createListener(callAbstractNode));

            /*
             * We also need to assert that all currently existing method end
             * states are added to the calling graph.
             */
            for (final State end : existingEnds) {
                final Collection<MethodGraphWorker> newWorkers =
                    this.getMethodGraph().newMethodEnd(existingMethodGraph, end, callAbstractNode);
                if (newWorkers != null) {
                    newTasks.addAll(newWorkers);
                }
            }
            result.addAll(newTasks);
        } else if (mergeResult.partnerEqualsMergedState()) {
            // we have a new start state, which we can connect to. We need to add this state and expand it, though.

            existingMethodGraph.newStartState(newStartState, this.getNodeToExpand().getNodeNumber());
            result.add(new StateNodeExpanderStandard(existingMethodGraph, existingMethodGraph.getStartNode()));

            /*
             * In a recursive scenario, the merge we just performed can remove nodes.
             * In particular, the node causing this merge might be removed.
             * In this case we obviously do not want to create a listener.
             */
            if (this.getMethodGraph().containsNode(callAbstractNode))
            {
                existingMethodGraph.addMethodEndListener(this.getMethodGraph().createListener(callAbstractNode));
            }
        } else {
            // the merge result is a new start state we need to add

            /*
             * We managed to create a state that is general enough for the old calls
             * to the method and the new one. As a result, the old state is replaced
             * by the merged state.
             */
            final State mergedState = mergeResult.getMergedState();

            final boolean removedAnnotation = mergedState.gc().x;
            assert (!removedAnnotation);

            existingMethodGraph.newStartState(mergedState, this.getNodeToExpand().getNodeNumber());
            result.add(new StateNodeExpanderStandard(existingMethodGraph, existingMethodGraph.getStartNode()));

            /*
             * In a recursive scenario, the merge we just performed can remove nodes.
             * In particular, the node causing this merge might be removed.
             * In this case we obviously do not want to create a listener.
             */
            if (this.getMethodGraph().containsNode(callAbstractNode))
            {
                existingMethodGraph.addMethodEndListener(this.getMethodGraph().createListener(callAbstractNode));
            }
        }
        return result;
    }

    /**
     * <p>
     * With IRs it is not trivial to merge two states, because each IR represents a different state position and the two
     * involved states may have different IRs. With different state positions, we cannot use the merger. Therefore, we
     * need to take care that both states have the same set of IRs.
     * </p>
     * <p>
     * First we try to merge NRIRs. Here the idea is to re-use already existing NRIRs, so that visible changes to some
     * pre-existing NRIR can also be used to track whatever a new NRIR is created for.
     * </p>
     * <p>
     * For every NRIR the existing start state, we copy the IRs that have no corresponding IR in the current state.
     * </p>
     * <p>
     * The merge process is repeated for the remaining (new?) NRIRs from this state, so that we can re-use as much NRIRs
     * from the existing start state as possible.
     * </p>
     * <p>
     * If all that did not help, we just add the IRs we could not merge/associate and start over with a new start state.
     * </p>
     * @param existingMethodGraph some existing method graph where we want to connect to
     * @return a pair, where the boolean denotes success and the second component is null if we can merge, otherwise
     * it contains jobs that need to be done
     */
    private Result handleIRs(final MethodGraph existingMethodGraph) {
        final State abstractedState = this.getNodeToExpand().getState();
        final State existingStartState = existingMethodGraph.getStartNode().getState();

        final Collection<InputRefRootPosition> thisPos = abstractedState.getInputReferences().getIRPositions(0);
        final Collection<InputRefRootPosition> thatPos = existingStartState.getInputReferences().getIRPositions(0);

        /*
         * The set of positions for the input references is the same, so we do
         * not need to do anything.
         */
        if (thisPos.equals(thatPos)) {
            return Result.JUST_MERGE;
        }

        final Collection<InputReference> thisIRs = new LinkedHashSet<>();
        thisIRs.addAll(abstractedState.getInputReferences().getNonRootInputReferences());
        thisIRs.addAll(abstractedState.getInputReferences().getRootInputReferences());
        final Collection<InputReference> thatIRs = new LinkedHashSet<>();
        thatIRs.addAll(existingStartState.getInputReferences().getNonRootInputReferences());
        thatIRs.addAll(existingStartState.getInputReferences().getRootInputReferences());

        final Collection<InputReference> handledThis = new LinkedHashSet<>();
        final Collection<InputReference> handledThat = new LinkedHashSet<>();

        // for every IR of this state, find a corresponding IR in that state
        for (final InputReference irThis : thisIRs) {
            final InputReference irThat = existingStartState.getInputReferences().getCorrespondingIR(irThis);
            if (irThat != null) {
                handledThis.add(irThis);
                handledThat.add(irThat);
            }
        }

        // now copy NRIRs from the other graph and merge NRIRs until all NRIRs from the call state are handled
        final Set<InputReference> copyTodo = new LinkedHashSet<>();
        final Map<NonRootInputReference, NonRootInputReference> mergeTodo = new LinkedHashMap<>();
        boolean changed;
        do {
            // try to merge NRIRs
            /*
             * We have some (new?) NRIR in this state, for which no corresponding NRIR exists in that state. Before
             * brutally adding this NRIR to that state, it might be a good idea to merge it with some other NRIR. This
             * identifies the pairs of NRIRs we can merge.
             */
            changed = this.mergeNRIRs(handledThis, copyTodo, existingMethodGraph, mergeTodo);

            // copy the additional NRIRs from that state to this state
            for (final InputReference ir : thatIRs) {
                if (!handledThat.contains(ir) && !copyTodo.contains(ir)) {
                    copyTodo.add(ir);
                    changed = true;
                }
            }
        } while (changed);

        /*
         * If we now do the work contained in mergeTodo and copyTodo, the local state contains all the NRIRs we need.
         * However, it might be that we need to copy a NRIR into the graph we try to connect to.
         */

        /*
         * Collect all IRs in this state for which we cannot find a corresponding IR in that state.
         */
        final Collection<InputReference> noPartner = new LinkedHashSet<>();
        for (final InputReference irThis : thisIRs) {
            if (handledThis.contains(irThis)) {
                continue;
            }
            noPartner.add(irThis);
        }

        if (existingMethodGraph.isFinished() && !noPartner.isEmpty()) {
            /*
             * We would need to modify a finished graph, which is a bad idea. Instead we just fail (and try to find
             * another graph to connect to or maybe create a new graph?)
             */
            return Result.FAIL;
        }

        // copy and merge as denoted in mergeTodo and copyTodo
        final State thisClone;
        String debugString = "";
        if (!copyTodo.isEmpty() || !mergeTodo.isEmpty()) {
            thisClone = abstractedState.clone();

            final String debugStringCopy = ConnectToMethodGraph.copyToAbstractedState(thisClone, existingStartState, copyTodo);
            if (Globals.DEBUG_COTTO) {
                debugString += debugStringCopy;
            }

            for (final Map.Entry<NonRootInputReference, NonRootInputReference> entry : mergeTodo.entrySet()) {
                final String debugStringMerge = ConnectToMethodGraph.doMerge(entry.getKey(), entry.getValue(), thisClone);
                if (Globals.DEBUG_COTTO) {
                    debugString += debugStringMerge;
                }
            }

            thisClone.gc();
        } else {
            thisClone = abstractedState;
        }

        if (noPartner.isEmpty()) {
            return new Result(thisClone, debugString);
        } else {
            // add additional NRIRs to the graph we try to connect to (this creates a new start state)

            final State thatClone = existingStartState.clone();

            // TODO this introduces abstraction (also see copyToAbstractedState)
            for (final InputReference ir : noPartner) {
                final AbstractVariableReference newRef = ConnectToMethodGraph.copyRenamed(thisClone, thatClone, ir.getReference());
                final InputReference clone = ir.clone();
                clone.replaceReference(newRef);
                thatClone.getInputReferences().add(clone);
            }

            return new Result(thisClone, thatClone, debugString);
        }
    }

    /**
     * Copy the given IRs from thatClone to the thisClone.
     * @param thisClone the working copy of the current state resulting out of a method call
     * @param thatState the state we try to connect to
     * @param copyTodo the IRs we need to copy
     * @return a debug string describing what we did
     */
    private static String copyToAbstractedState(
        final State thisClone,
        final State thatState,
        final Collection<InputReference> copyTodo)
    {
        // TODO this introduces abstraction

        String debugString;
        if (Globals.DEBUG_COTTO) {
            debugString = "";
        } else {
            debugString = null;
        }

        for (final InputReference ir : copyTodo) {
            final InputReference clone = ir.clone();
            AbstractVariableReference newRef;

            // for RootIRs use the reference from the current state (as it already exists)
            if (ir instanceof RootInputReference) {
                final RootInputReference rootIR = (RootInputReference) ir;
                newRef = thisClone.getReference(rootIR.getPosition());
            } else {
                newRef = ConnectToMethodGraph.copyRenamed(thatState, thisClone, ir.getReference());
            }
            clone.replaceReference(newRef);
            thisClone.getInputReferences().add(clone);

            if (Globals.DEBUG_COTTO) {
                debugString += "copied " + ir + "\n";
            }
        }

        return debugString;
    }

    /**
     * For an abstract instance (or some primitive value) copy the abstract
     * information (type, existence, (non-)tree, (a)cyclic) from one state to
     * the other and in case of conflicts rename the reference.
     * @param fromState the state to copy from
     * @param toState the state to copy to
     * @param ref the reference to copy
     * @return the corresponding reference in toState
     */
    private static AbstractVariableReference copyRenamed(
        final State fromState,
        final State toState,
        final AbstractVariableReference ref)
    {
        if (ref.isNULLRef()) {
            return ref;
        }

        final AbstractVariable origVar = fromState.getAbstractVariable(ref);

        AbstractVariableReference newRef;
        if (toState.getReferences().containsKey(ref)) {
            newRef = AbstractVariableReference.create(ref);
        } else {
            newRef = ref;
        }

        if (ref.pointsToReferenceType()) {
            if (origVar == null) {
                assert (fromState.getHeapAnnotations().isMaybeExisting(ref));
            } else {
                newRef = toState.createReferenceAndAdd(new AbstractInstance(), OperandType.ADDRESS);
            }
            fromState.getHeapAnnotations().copyUnaryAnnotationsToState(ref, toState, newRef);
        } else {
            toState.addAbstractVariable(newRef, origVar.clone());
        }
        return newRef;
    }

    /**
     * @return the node with an outgoing call abstract edge
     */
    private Node findCallAbstractNode() {
        Node currentNode = this.getNodeToExpand();
        while (true) {
            if (!this.getMethodGraph().containsNode(currentNode)) {
                return null;
            }
            final Set<Edge> inEdges = currentNode.getInEdges();
            assert (inEdges.size() == 1) : inEdges;
            final Edge inEdge = inEdges.iterator().next();
            if (inEdge.getLabel() instanceof CallAbstractEdge) {
                return inEdge.getStart();
            }
            currentNode = inEdge.getStart();
        }
    }

    /**
     * Find pairs of NRIRs that can be merged, but do not do the actual merge(s).
     * @param handled the IRs that we can already associate with some IR of an existing start state. This will be
     * updated so that the NRIRs from the result are also included.
     * @param copiedIRs NRIRs we copied from the method graph we want to connect to
     * @param otherMethodGraph the graph we try to connect to
     * @param mergeTodo a map containing pairs x -> y meaning the NRIR x should be merged into the NRIR y, will be updated
     * @return true iff we added an entry
     */
    private boolean mergeNRIRs(
        final Collection<InputReference> handled,
        final Set<InputReference> copiedIRs,
        final MethodGraph otherMethodGraph,
        final Map<NonRootInputReference, NonRootInputReference> mergeTodo)
    {
        final State state = this.getNodeToExpand().getState();

        boolean added = false;

        final Collection<NonRootInputReference> nrirs = new LinkedHashSet<>();
        nrirs.addAll(state.getInputReferences().getNonRootInputReferences());
        for (final InputReference ir : copiedIRs) {
            if (ir instanceof NonRootInputReference) {
                nrirs.add((NonRootInputReference) ir);
            }
        }

        // get all pairs of NRIRs (for (x, y) we do not get (y, x)!)
        for (final Pair<NonRootInputReference, NonRootInputReference> pair : Collection_Util.getPairs(nrirs)) {
            final NonRootInputReference refA = pair.x;
            final NonRootInputReference refB = pair.y;

            if (!refA.sameType(refB)) {
                // we are not allowed to merge
                continue;
            }

            if (!refA.mergeOK(refB)) {
                continue;
            }

            /*
             * Maybe it already is possible to associate at least one of the NRIRs with a NRIR of the existing start
             * state?
             */
            final boolean wasHandledA = handled.contains(refA);
            final boolean wasHandledB = handled.contains(refB);

            boolean mergeIntoA;
            /*
             * copiedA handledA copiedB handledB mergeIntoA
             *       1        0       1        0          -
             *       0        1       1        0          -
             *       0        0       1        0          0
             *       1        0       0        1          -
             *       0        1       0        1          -
             *       0        0       0        1          0
             *       1        0       0        0          1
             *       0        1       0        0          1
             *       0        0       0        0         0/1
             */
            if (copiedIRs.contains(refA) || wasHandledA) {
                if (copiedIRs.contains(refB) || wasHandledB) {
                    continue;
                }
                mergeIntoA = true;
            } else if (copiedIRs.contains(refB) || wasHandledB) {
                if (copiedIRs.contains(refA) || wasHandledA) {
                    continue;
                }
                mergeIntoA = false;
            } else {
                mergeIntoA = true;
            }

            NonRootInputReference refFrom;
            NonRootInputReference refInto;
            if (mergeIntoA) {
                refInto = refA;
                refFrom = refB;
            } else {
                refInto = refB;
                refFrom = refA;
            }

            handled.add(refFrom);
            mergeTodo.put(refFrom, refInto);
            added = true;
        }

        return added;
    }

    /**
     * Note: The given state will be changed, so clone the original state before providing it here!
     * Merges refFrom into refInto.
     * @param refFrom a NRIR
     * @param refInto another NRIR
     * @param state the state containing the NRIRs, will be updated
     * @return a debug string describing what we did
     */
    private static String doMerge(
        final NonRootInputReference refFrom,
        final NonRootInputReference refInto,
        final State state)
    {
        final String debugString;
        if (Globals.DEBUG_COTTO) {
            debugString = "merged " + refFrom + " into " + refInto + "\n";
        } else {
            debugString = null;
        }
        refInto.add(refFrom);
        state.getHeapAnnotations().mergeAnnotationsForNRIRMerge(state, refFrom.getReference(), refInto.getReference());
        if (state.getHeapAnnotations().isMaybeExisting(refInto.getReference())) {
            state.removeAbstractVariable(refInto.getReference());
        }

        final boolean removed = state.getInputReferences().removeNRIR(refFrom);
        assert (removed);
        state.replaceReference(refFrom.getReference(), refInto.getReference());

        state.gc();

        return debugString;
    }
}

class Result {
    public static final Result FAIL = new Result();
    public static final Result JUST_MERGE = new Result();

    private State thisClone;
    private State thatClone;

    private String debugString;

    public Result() {
    }

    public Result(final State thisCloneParam, final String debugStringParam) {
        this.thisClone = thisCloneParam;
        this.debugString = debugStringParam;
    }

    public Result(final State thisCloneParam, final State thatCloneParam, final String debugStringParam) {
        this.thisClone = thisCloneParam;
        this.thatClone = thatCloneParam;
        this.debugString = debugStringParam;
    }

    public boolean newCallStateThenMerge() {
        return this.thisClone != null && this.thatClone == null;
    }

    public boolean newCallStateNewStartStateThenMerge() {
        return this.thisClone != null && this.thatClone != null;
    }

    public State getThisClone() {
        return this.thisClone;
    }

    public State getThatClone() {
        return this.thatClone;
    }

    /**
     * @return a debug string which is written to the instance edge
     */
    public String getDebugString() {
        return this.debugString.replace("\n", "\\n");
    }
}
