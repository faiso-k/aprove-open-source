package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.io.*;
import java.util.*;
import java.util.Map.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;
import static java.util.stream.Collectors.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Util.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Consistency.*;
import aprove.verification.oldframework.Bytecode.Graphs.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * This class implements the finite interpretation graph of one method.
 * @author Marc Brockschmidt
 * @author Christian von Essen
 * @author Carsten Otto
 * @author Fabian K&uuml;rten
 */
public final class MethodGraph extends JBCGraph implements MethodEndNotifier, Exportable {
    /**
     * The method this graph is built for.
     */
    private final IMethod parsedMethod;

    /**
     * Remember the nodes that were hidden during construction.
     */
    private final Set<Node> hidden = new LinkedHashSet<>();

    /**
     * A list of states that use the OpCode. This is allowing us to find all
     * possibly matching states when trying to find instances or merge. The
     * second component of the pair is true iff some exception is thrown.
     */
    private final CollectionMap<Pair<OpCode, Boolean>, Node> nodesForOpcode;

    /**
     * Lock used to control access to the graph.
     */
    private final ReentrantReadWriteLock graphLock;

    /**
     * The method end states of this method.
     */
    private final Set<State> methodEndStates = new LinkedHashSet<>();

    /**
     * The listeners of this graph. Thy will be notified everytime the
     * methodEndStates change.
     */
    private final Set<MethodEndListener> methodEndListeners = new LinkedHashSet<>();

    /**
     * The start node of this graph.
     */
    private Node startNode;

    /**
     * The termination graph connecting all MethodGraphs.
     */
    private final TerminationGraph terminationGraph;

    /**
     * The threading policy (queue) for this method graph.
     */
    private final ThreadingPolicy policy;

    /**
     * Remember states that will be added later and need to be merged.
     *
     * OpCode o |-> (State s1, {(Node n, EdgeInformation e, State s2)})
     *
     * For o we know that s1 needs to be added later. If s1 == s2 then s1 is connected to n via e. If s1 != s2 then s2
     * is connected to n via e and s2 is an instance of s1.
     */
    private final Map<OpCode, Pair<State, Collection<Triple<Node, EdgeInformation, State>>>> delayedMerges;

    /**
     * Track how many workers are scheduled for this graph, but not yet done.
     */
    private final AtomicInteger waitingWorkers;

    /**
     * Some NonTerm workers that are run as soon as all graphs are finished.
     */
    private final Collection<NonTermWorker> nonTermQueue;

    /**
     * If set to true, construction of this method graph is finished and nothing will be added anymore.
     */
    private boolean finished;

    /**
     * In how many states does the given method occur somewhere on the call stack?
     */
    private ConcurrentHashMap<MethodIdentifier, AtomicInteger> stateCountForLibraryMethods = new ConcurrentHashMap<>();

    /**
     * How often was the given method invoked?
     */
    private ConcurrentHashMap<MethodIdentifier, AtomicInteger> invokingStates = new ConcurrentHashMap<>();

    /**
     * Private constructor.
     * @param startNodeParam the start node of this graph
     * @param terminationGraphParam the termination graph
     */
    private MethodGraph(final Node startNodeParam, final TerminationGraph terminationGraphParam) {
        this.graphLock = new ReentrantReadWriteLock(true);
        this.nodesForOpcode = new CollectionMap<>(CollectionCreator.concurrentHashSet());
        this.startNode = startNodeParam;
        final OpCode curOpcode = startNodeParam.getState().getCurrentOpCode();
        this.parsedMethod = curOpcode.getMethod();
        this.terminationGraph = terminationGraphParam;
        if (this.getJBCOptions().multithreaded) {
            this.policy = new FairQueuingPolicy(this.terminationGraph.getThreadingPolicy());
        } else {
            this.policy = null;
        }
        this.addNode(startNodeParam);
        this.nodesForOpcode.add(
            new Pair<>(curOpcode, startNodeParam.getState().getCurrentStackFrame().hasException()),
            startNodeParam);
        this.delayedMerges = new LinkedHashMap<>();
        this.waitingWorkers = new AtomicInteger();
        this.nonTermQueue = new LinkedHashSet<>();
    }

    /**
     * Create an (unfinished) MethodGraph and set up a start state in it.
     * @param state some state.
     * @param terminationGraphParam the termination graph
     * @return the created MethodGraph
     */
    public static MethodGraph create(final State state, final TerminationGraph terminationGraphParam) {
        final Node startNode = new Node(state);
        final MethodGraph graph = new MethodGraph(startNode, terminationGraphParam);
        return graph;
    }

    /**
     * Do not use!
     * Use {@link MethodGraph#removeNode(Node, Collection)} instead
     */
    @Override
    @Deprecated
    public boolean removeNode(Node node) {
        throw new UnsupportedOperationException("removeNode(Node) is not allowed in MethodGraph, please use removeNode(Node, Collection<MethodGraphWorker>)");
    }

    /**
     * Needs the write lock of this graph.
     * Removes the node from the graph, and all accompanying data structures in this class,
     *
     * tries to remove it from methodEndStates,
     * tries to unregister MethodEndListeners
     *
     * @param node the node to remove
     * @param tasks the tasks that require locks we could not obtain are added to this list
     * @return true if the node was removed from the graph (but not necessarily from all other data structures)
     */
    public boolean removeNode(Node node, Collection<MethodGraphWorker> tasks) {
        assert(graphLock.isWriteLockedByCurrentThread());
        //remove from nodesForOpcodes
        final State state = node.getState();
        final OpCode opCode = state.getCurrentOpCode();
        Boolean hasException = Boolean.FALSE;
        if (opCode != null) {
            hasException = state.getCurrentStackFrame().hasException();
        }
        final Pair<OpCode, Boolean> pair = new Pair<>(opCode, hasException);
        this.nodesForOpcode.removeFromCollection(pair, node);

        //remove from methodEndStates
        this.methodEndStates.remove(state);

        unregisterMethodEndListeners(node, tasks);
        node.hide();
        this.hidden.add(node);
        return removeNodeInternal(node);
    }

    private void unregisterMethodEndListeners(Node node, Collection<MethodGraphWorker> tasks) {
        for (final Edge edge : node.getOutEdges()) {
            if (edge.getLabel() instanceof CallAbstractEdge) {
                final Collection<MethodGraph> graphs = this.terminationGraph.getMethodGraphs();
                for (final MethodGraph mg : graphs) {
                    if (mg.getGraphLock().writeLock().tryLock()) {
                        try {
                            mg.removeMethodEndListener(node);
                        } finally {
                            mg.getGraphLock().writeLock().unlock();
                        }
                    } else {
                        // create new task
                        final RemoveMethodEndListenerWorker task = new RemoveMethodEndListenerWorker(mg, node);
                        tasks.add(task);
                    }
                }
            }
        }
    }

    /**
     * Needs the write lock of this Graph, if the node has methodEndListener in other graphs attached to it, those locks are needed as well.
     * Removes the node from the graph, and all accompanying data structures in this class,
     *
     * removes it from methodEndStates, unregisters MethodEndListeners
     *
     * @param node the node to remove
     * @return true if the node was removed from the graph
     */
    public boolean removeNodeWithLocks(Node node) {
        return this.removeNode(node, Collections.emptyList());
    }

    @Override
    public void removeEdge(Edge edge) {
        assert(graphLock.isWriteLockedByCurrentThread());
        edge.getStart().hideOutgoingEdge(edge);
        edge.getEnd().hideIncomingEdge(edge);
    }

    /**
     * Needs the write lock of this graph.
     * Add a new edge to the graph, but check if the edge is still valid (i.e.
     * the source still exists) and update our local caches and evaluation
     * history for the graph change.
     * @param edge the edge to add
     * @return true if the edge was added, false if it was already in the graph
     */
    @Override
    public boolean addEdge(Edge edge) {
        assert(graphLock.isWriteLockedByCurrentThread());
        if (super.addEdge(edge)) {
            Node endNode = edge.getEnd();
            Node startNode = edge.getStart();
            EdgeInformation label = edge.getLabel();
            if (Globals.useAssertions) {
                assert (!this.finished || endNode.getState().callStackEmpty());
                assert (!(label instanceof MethodReturnEdge));
                if (label instanceof InstanceEdge) {
                    for (final Edge e : endNode.getInEdges()) {
                        final EdgeInformation otherLabel = e.getLabel();
                        if ((otherLabel instanceof RefinementOrSplitEdge)) {
                            this.dumpImage();
                            assert (false) : e;
                        }

                    }
                }
            }
            /*
             * The target state was obtained by evaluation, instantiation, or
             * initialization change. Update history and our cache of merge
             * candidates:
             */
            if (label instanceof EvaluationEdge
                || label instanceof InstanceEdge
                || label instanceof InitializationStateChange)
            {
                State endState = endNode.getState();
                OpCode opCode = endState.getCurrentOpCode();
                Boolean hasException = Boolean.FALSE;
                if (opCode != null) {
                    hasException = endState.getCurrentStackFrame().hasException();
                }
                Pair<OpCode, Boolean> pair = new Pair<>(opCode, hasException);
                this.nodesForOpcode.add(pair, endNode);
                if (label instanceof InitializationStateChange) {
                    /*
                     * It does not make sense to merge with a state which only has
                     * successors with incompatible initialization states
                     */
                    this.nodesForOpcode.removeFromCollection(pair, startNode);
                }
                if (label instanceof InstanceEdgeTryToConnect) {
                    this.nodesForOpcode.removeFromCollection(pair, endNode);
                }
            // always directly hide DebugEdges
            } else if (label instanceof DebugEdge) {
                this.removeEdge(edge);
                Node toRemove;
                if (label instanceof FailedIntersectionEdge || label instanceof FailedRefinementEdge) {
                    //also remove the end node
                    toRemove = edge.getEnd();
                    assert(toRemove.getOutEdges().isEmpty());
                    this.removeNodeWithLocks(toRemove);
                }
            }
            return true;
        } else {
            return false;
        }
    }

    /**
     * This method prepares adding the new state, so that all collected graph
     * updates (which require a lock) can be done without computing much. The
     * exact behaviour depends on the shape of the new state and the edge used
     * to connect the new state. Besides adding the new state and edge, a merge
     * might be performed. Furthermore, incoming instance edges might be added.
     * If the new state is a method invocation, a new method graph might be
     * created. Furthermore, new end states are propagated to the associated
     * invoking states.
     * @param expandedStateNode old state from which a successor was generated
     * @param newState the new, freshly-generated successor
     * @param newEdge edge describing the operation used to obtain
     * <code>newState</code> from <code>expandedState</code>.
     * @return null iff the state could not be added (because the graph was
     * changed during the computation) so that we need to try adding the state
     * again. Otherwise a collection of tasks, (i) new leafs that need to be
     * expanded and (ii) states which still need to be added to their graph (an
     * empty collection is returned if nothing needs to be done)
     */
    public Collection<MethodGraphWorker> addStateToGraph(
        final Node expandedStateNode,
        final State newState,
        final EdgeInformation newEdge)
    {
        final Collection<MethodGraphWorker> res = new LinkedList<>();
        //Check if we still need to do this:
        if (!this.containsNode(expandedStateNode)) {
            return res;
        }

        if (checkNeedForMethodSummaries(newState, res)) {
            return res;
        }

        final Collection<State> statesToAdd = new LinkedList<>();
        final Collection<Triple<State, EdgeInformation, State>> edgesToAdd = new LinkedList<>();
        final Collection<State> newStatesForQueue = new LinkedList<>();
        final Collection<Node> nodesWithChangedSuccs = new LinkedList<>();
        final State newMethodEndState;
        final State expandedState = expandedStateNode.getState();

        //Always add the new node and the fitting edge:
        statesToAdd.add(newState);
        edgesToAdd.add(new Triple<>(expandedState, newEdge, newState));

        /*
         * We do not need to invest more work into the state, if it is the
         * result of failed refinement or if it corresponds to a program end.
         */
        if (newEdge instanceof DebugEdge) {
            //Do nothing else
            newMethodEndState = null;
        } else if (newState.callStackEmpty()) {
            /*
             * The new state has an empty callstack, hence the previous state
             * is a method end state.
             * In this case we will mark the previous state accordingly.
             */
            newMethodEndState = expandedState;
        } else if (newEdge instanceof CallAbstractEdge) {
            // don't merge!
            newMethodEndState = null;
            // but expand later
            newStatesForQueue.add(newState);
        } else if (newEdge instanceof MethodStartEdge || newEdge instanceof InstanceEdgeMethodStartMerge) {
            newMethodEndState = null;

            boolean isTailCall = false;
            if (newEdge instanceof InstanceEdgeMethodStartMerge) {
                isTailCall = false;
            }
            if (newEdge instanceof MethodStartEdge) {
                isTailCall = ((MethodStartEdge) newEdge).isTailCall();
            }
            JBCMergeResult bestResult = null;
            if (this.getJBCOptions().mergeCalls || terminationGraph.getGoal() != HandlingMode.Termination) { //always merge calls in complexity analysis
                if (MethodStart.doSplit(newState, this.getJBCOptions(), isTailCall)) {
                    final Collection<Node> candidates =
                        this.findCandidateNodesForMerge(newState, expandedStateNode, newEdge);
                    bestResult = this.findBestMergePartner(newState, Double.MAX_VALUE, candidates);
                }
            }
            if (bestResult != null) {
                final boolean couldAddMergeResults =
                    this.handleMergeResult(
                        newState,
                        bestResult,
                        expandedStateNode,
                        statesToAdd,
                        edgesToAdd,
                        newStatesForQueue,
                        nodesWithChangedSuccs,
                        true);
                if (!couldAddMergeResults) {
                    return null;
                }
            } else {
                newStatesForQueue.add(newState);
            }
        } else {
            // Not a special state, so check if we need to merge:
            newMethodEndState = null;

            /*
             * Find out how important it is to merge this state with another
             * one. maximalMergeCosts = NULL enforces merging, 0 only
             * searches for instances and 0<k finds merge partners with
             * merge costs lower than k.
             */
            JBCMergeResult bestResult = null;
            if (this.getJBCOptions().tryMerging) {
                Double maximalMergeCosts = this.getMaximalAllowedMergeCosts(newEdge, newState, expandedStateNode);
                final boolean needToMerge = maximalMergeCosts == null;
                final boolean tryToMerge = needToMerge || maximalMergeCosts.compareTo(0.0) > 0;
                final boolean tryToFindInstance = tryToMerge || this.getJBCOptions().outgoingInstanceFinder();
                if (tryToFindInstance) {
                    final Collection<Node> candidates =
                        this.findCandidateNodesForMerge(newState, expandedStateNode, newEdge);

                    // first try to find an instance
                    bestResult = this.findBestMergePartner(newState, 0.0, candidates);
                    if (bestResult == null
                        && needToMerge
                        && newEdge instanceof EvaluationEdge
                        && this.delayMerge(expandedStateNode, candidates, newState)
                        && this.handleDelayedMerge(expandedStateNode, newState, newEdge))
                    {
                        // no instance, but we have to merge. The merge is delayed
                        return res;
                    }

                    if (bestResult == null && tryToMerge) {
                        //instance didn't work, try merge
                        bestResult = this.findBestMergePartner(newState, maximalMergeCosts, candidates);
                    }
                }
                if (bestResult == null && needToMerge) {
                    if (!this.containsNode(expandedStateNode)) {
                        /*
                         * No problem, we changed the graph anyway so there's no
                         * need to do anything with the state we tried to
                         * evaluate.
                         */
                        return null;
                    }
                    // Oh my god we needed to merge but couldn't: DIE!
                    //this.dumpImage();
                    assert (false) : "Have to merge, but wasn't able to find a merge"
                    + "partner for child of node "
                    + expandedStateNode.getNodeNumber()
                    + ", which looks like this:\n"
                    + newState;
                }
            }

            if (bestResult != null) {
                this.getGraphLock().readLock().lock();
                try {
                    final Node mergePartnerNode = this.getNode(bestResult.getPartnerState());
                    IMethod startMethod = this.getTerminationGraph().getStartGraph().getParsedMethod();
                    if (mergePartnerNode != null
                        && this.getJBCOptions().tryNontermProofs()
                        && bestResult.partnerEqualsMergedState()
                        && startMethod.equals(this.getParsedMethod())
                        && expandedStateNode
                            .getState()
                            .getHeapAnnotations()
                            .getCyclicStructures()
                            .getCyclicRefs()
                            .size() < 3)
                    {
                        //The two states are identical. WHOA!

                        //Only do this if no method calls happen or the called methods are pure:
                        final EdgeFilter onlyPureMethodCallsFilter = new EdgeFilter() {
                            @Override
                            public boolean selectEdge(final Node from, final Node to, final EdgeInformation e) {
                                //Only allow pure methods to be called:
                                if (e instanceof MethodSkipEdge && !((MethodSkipEdge) e).callIsPure()) {
                                    return false;
                                }
                                return true;
                            }
                        };

                        if (JBCGraph.hasPath(mergePartnerNode, expandedStateNode, true, onlyPureMethodCallsFilter)
                            && JBCGraph
                                .hasPath(this.getStartNode(), expandedStateNode, true, onlyPureMethodCallsFilter))
                        {
                            if (NonTermWorker.numberOfStartedWorkers < NonTermWorker.MAX && expandedStateNode.getNodeNumber() < 500) {
                                if (this.getTerminationGraph().getJBCOptions().tryLoopingNontermProofs()) {
                                    LoopingNonTermWitnessFinder.runNow(this, expandedStateNode, mergePartnerNode, res);
                                    NonTermWorker.numberOfStartedWorkers++;
                                }
                                if (this.getTerminationGraph().getJBCOptions().tryNonLoopingNontermProofs()) {
                                    NonLoopingNonTermWitnessFinder.runNow(this, expandedStateNode, mergePartnerNode,
                                        res);
                                    NonTermWorker.numberOfStartedWorkers++;
                                }
                            } else {
                                if (this.getTerminationGraph().getJBCOptions().tryLoopingNontermProofs()) {
                                    LoopingNonTermWitnessFinder.runWhenFinished(this, expandedStateNode,
                                        mergePartnerNode);
                                }
                                if (this.getTerminationGraph().getJBCOptions().tryNonLoopingNontermProofs()) {
                                    NonLoopingNonTermWitnessFinder.runWhenFinished(this, expandedStateNode,
                                        mergePartnerNode);
                                }
                            }
                        }
                    }
                    final boolean couldAddMergeResults =
                        this.handleMergeResult(
                            newState,
                            bestResult,
                            expandedStateNode,
                            statesToAdd,
                            edgesToAdd,
                            newStatesForQueue,
                            nodesWithChangedSuccs,
                            false);
                    if (!couldAddMergeResults) {
                        return null;
                    }
                } finally {
                    this.getGraphLock().readLock().unlock();
                }
            } else {
                boolean needsExpansion;
                /*
                 * If this state was obtained by evaluation, try to find
                 * instances:
                 */
                if (newEdge instanceof EvaluationEdge) {
                    needsExpansion = findInstacesAndCreateEdges(
                            newState, newEdge, false, Collections.emptyList(), nodesWithChangedSuccs, edgesToAdd);
                } else {
                    needsExpansion = true;
                }

                if (needsExpansion) {
                    newStatesForQueue.add(newState);
                }
            }
        }

        final Collection<MethodGraphWorker> tasks =
            this.performChanges(
                expandedStateNode,
                statesToAdd,
                edgesToAdd,
                newStatesForQueue,
                nodesWithChangedSuccs,
                newMethodEndState);
        if (tasks == null) {
            return null;
        }
        res.addAll(tasks);

        return res;
    }

    /**
     * Checks whether we should use summaries for methods, and does the necessary changes to the graph.
     * Only is done when {@link aprove.runtime.Options.JBCAnalysisOptions#summarizeRecursiveMethods}
     * or {@link aprove.runtime.Options.JBCAnalysisOptions#summarizeLibraryCallsWithMoreStates} are set.
     * @see aprove.runtime.Options.JBCAnalysisOptions.AvailableOptions#summarize_recursive_methods
     * @see aprove.runtime.Options.JBCAnalysisOptions.AvailableOptions#summarize_library_calls_with_more_states
     * @param newState state added to the graph
     * @param res when summarizing is done, needed workers are added here
     * @return whether summarizing was done
     */
    private boolean checkNeedForMethodSummaries(State newState, Collection<MethodGraphWorker> res) {
        TerminationGraph termG = newState.getTerminationGraph();
        JBCOptions options = this.getJBCOptions();
        ClassPath cp = newState.getClassPath();
        List<StackFrame> stackFrames = new ArrayList<>(newState.getCallStack().getStackFrameList());
        Collections.reverse(stackFrames);
        if (options.summarizeRecursiveMethods()) {
            OpCode oc = newState.getCurrentOpCode();
            if (oc != null && oc.getPos() == 0) {
                IMethod pm = oc.getMethod();
                if (!termG.getPredefinedMethods().hasOverridingMethod(pm, newState)) {
                    StackFrame cf = newState.getCurrentStackFrame();
                    boolean isRecursiveCall = stackFrames.stream().anyMatch(x -> x != cf && x.getMethod().equals(pm));
                    if (isRecursiveCall) {
                        termG.getPredefinedMethods().forceOverwriteWithDefaultSummary(pm, termG.getGoal(), "recursion");
                        res.addAll(removeAllInvokationsOf(pm.getMethodIdentifier()));
                        return true;
                    }
                }
            }
        }
        if (options.getSummarizeLibraryCallsWithMoreStates() > 0) {
            for (StackFrame sf: stackFrames) {
                MethodIdentifier mid = sf.getMethod().getMethodIdentifier();
                if (cp.isLibraryClass(mid.getClassName()) && !termG.getPredefinedMethods().hasOverridingMethod(sf.getMethod(), newState)) {
                    int stateCount = stateCountForLibraryMethods.computeIfAbsent(mid, i -> new AtomicInteger()).incrementAndGet();
                    int invokingStateCount = invokingStates.computeIfAbsent(mid, i -> new AtomicInteger()).get();
                    int relativeStateCount;
                    if (invokingStateCount > 0) {
                        relativeStateCount = stateCount / invokingStateCount;
                    } else {
                        relativeStateCount = stateCount;
                    }
                    if (relativeStateCount > options.getSummarizeLibraryCallsWithMoreStates()) {
                        res.addAll(removeAllInvokationsOf(mid));
                        IMethod pm = cp.getClass(mid.getClassName()).getMethodRecursively(mid);
                        if (termG.getPredefinedMethods().overwriteWithDefaultSummary(pm, termG.getGoal(), "complex library call")) {
                            res.addAll(removeAllInvokationsOf(mid));
                            return true;
                        }
                    }
                }
            }
            if (newState.getCurrentOpCode() != null && newState.getCurrentOpCode().getPos() == 0) {
                MethodIdentifier mid = newState.getCurrentStackFrame().getMethod().getMethodIdentifier();
                invokingStates.computeIfAbsent(mid, i -> new AtomicInteger()).incrementAndGet();
            }
        }
        return false;
    }

    /**
     * Removes the subtree below any node the invokes a Method, and creates new {@link StateNodeExpanderStandard} for thes nodes
     * @param mid identifier of the method to be removed
     * @return the set of workers needed for the removing of the method and reevaluating of nodes
     */
    public Collection<MethodGraphWorker> removeAllInvokationsOf(MethodIdentifier mid) {
        Set<Node> toEvaluate = new LinkedHashSet<>();
        // collect all nodes invoking id
        graphLock.readLock().lock();
        try {
            for (Node n: this.getNodes()) {
                OpCode oc = n.getState().getCurrentOpCode();
                if (oc != null && oc.getPos() == 0 && oc.getMethod().getMethodIdentifier().equals(mid)) {
                    for (Edge e: n.getInEdges()) {
                        toEvaluate.add(e.getStart());
                    }
                }
            }
            // if x and c invoke mid and x reaches c, just keep x
            Iterator<Node> it = toEvaluate.iterator();
            while (it.hasNext()) {
                Node c = it.next();
                if (toEvaluate.stream().anyMatch(x -> x != c && hasPath(x, c, false, null))) {
                    it.remove();
                }
            }
        } finally {
            graphLock.readLock().unlock();
        }
        // we have to re-evaluate all nodes we collected
        Set<MethodGraphWorker> res = new LinkedHashSet<>();
        for (Node node: toEvaluate) {
            res.add(new StateNodeExpanderStandard(this, node));
        }
        // remove all subgraphs rooted by the nodes we collected
        res.addAll(removeSubgraphSafely(toEvaluate, Collections.emptyList()));
        if (Globals.useAssertions) {
            graphLock.readLock().lock();
            // check if any node where mid is on the stack survived
            try {
                for (Node n: this.getNodes()) {
                    for (StackFrame sf: n.getState().getCallStack().getStackFrameList()) {
                        // TODO when things get more stable, this should become a warning
                        // instead of an assertion because it's not required for correctness
                        assert !sf.getMethod().getMethodIdentifier().equals(mid);
                    }
                }
            } finally {
                graphLock.readLock().unlock();
            }
        }
        return res;
    }

    /**
     * @param expandedStateNode old state from which a successor was generated
     * @param newState the new, freshly-generated successor
     * @param newEdge edge describing the operation used to obtain
     * <code>newState</code> from <code>expandedState</code>.
     * @return true only if we delayed the merge and do not need to do anything more
     */
    private
        boolean
        handleDelayedMerge(final Node expandedStateNode, final State newState, final EdgeInformation newEdge)
    {
        final OpCode opCode = newState.getCurrentOpCode();
        graphLock.writeLock().lock();
        try {
            Pair<State, Collection<Triple<Node, EdgeInformation, State>>> oldDelayed = this.delayedMerges.get(opCode);

            // throw out the entries that correspond to deleted nodes
            if (oldDelayed != null) {
                oldDelayed.y.removeIf(t -> !this.containsNode(t.x));

                if (oldDelayed.y.isEmpty()) {
                    this.delayedMerges.remove(opCode);
                    oldDelayed = null;
                }
            }

            if (oldDelayed == null) {
                /*
                 * this is the first state we want to delay (for the current opcode)
                 * Nothing to do right now, just add and merge newState later (as a successor of
                 * expandedStateNode)
                 */
                final Triple<Node, EdgeInformation, State> triple = new Triple<>(expandedStateNode, newEdge, newState);
                final Collection<Triple<Node, EdgeInformation, State>> set = new LinkedHashSet<>();
                set.add(triple);
                this.delayedMerges.put(opCode, new Pair<>(newState, set));

                if (JBCOptions.DEBUG_DELAYMERGE) {
                    System.out.println("Delaying merge of successor of "
                            + expandedStateNode
                            + " (which has hashCode "
                            + newState.hashCode()
                            + ")");
                }
                return true;

            } else {
                // there already is some delayed state
                final State oldDelayedState = oldDelayed.x;
                assert (!oldDelayed.y.isEmpty());

                // merge the two states we want to delay and delay the resulting state instead
                final PathMerger merger = new PathMerger(newState);

                // we will merge the delayed state later, where we will also increase counters if needed
                merger.setDoNotIncreaseCounters();

                if (merger.merge(oldDelayedState)) {
                    final JBCMergeResult mr = merger.getResult();
                    if (!mr.partnerEqualsMergedState()) {
                        // delay the merged state (by changing the information stored in this.delayMerges)
                        oldDelayed.x = mr.getMergedState();
                    }
                    oldDelayed.y.add(new Triple<>(expandedStateNode, newEdge, newState));

                    if (JBCOptions.DEBUG_DELAYMERGE) {
                        System.out.println("When trying to delay successor of "
                                + expandedStateNode
                                + " (which has hashCode "
                                + newState.hashCode()
                                + ") we merged with the old delayed state (hashCode "
                                + oldDelayedState.hashCode()
                                + ") and obtained a new state with hashCode "
                                + mr.getMergedState().hashCode());
                    }

                    // nothing more to do right now
                    return true;
                }
            }
            return false;
        } finally {
            graphLock.writeLock().unlock();
        }
    }

    /**
     * @param expandedStateNode the state expanded to newState
     * @param candidates other nodes with which we would try to merge newState
     * @param newState the state expanded from newState, normally enforcing a merge
     * @return true if we want to delay the merge of newState
     */
    private boolean delayMerge(final Node expandedStateNode, final Collection<Node> candidates, final State newState) {
        if (!this.getJBCOptions().delayMerge) {
            return false;
        }
        this.graphLock.readLock().lock();
        try {
            return DelayedMerge.delayMerge(expandedStateNode, candidates, newState, this);
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * @param newState a (new) state that is being merged.
     * @param mergeResult result of a merge below maximal costs.
     * @param expandedStateNode the node for which we introduce new successors.
     * @param statesToAdd collection of states that should be added to the
     * graph.
     * @param edgesToAdd collection of edges that should be added to the graph.
     * @param newStatesForQueue collection of states that should be put into the
     * queue for further expansion.
     * @param nodesWithChangedSuccs collection of nodes that get a new successor
     * (by instantiation/merge) and thus may lead to deletion of the subgraph
     * starting in them.
     * @param methodStartMerge if set, use a special kind of instance edges
     * @return true iff we can construct the needed new nodes and edges to
     * represent the merge in this state.
     */
    private boolean handleMergeResult(
        final State newState,
        final JBCMergeResult mergeResult,
        final Node expandedStateNode,
        final Collection<State> statesToAdd,
        final Collection<Triple<State, EdgeInformation, State>> edgesToAdd,
        final Collection<State> newStatesForQueue,
        final Collection<Node> nodesWithChangedSuccs,
        final boolean methodStartMerge)
    {
        final State mostSimilarState = mergeResult.getPartnerState();

        //The state was already removed from the graph again, so we need
        //to try again:
        final Node mostSimilarNode = this.getNode(mostSimilarState);
        if (mostSimilarNode == null) {
            return false;
        }

        /*
         * If the merger noted that the new state is an instance of the
         * most similar state, add an instance edge from the former
         * to the latter:
         */
        if (mergeResult.partnerEqualsMergedState()) {
            if (methodStartMerge) {
                edgesToAdd.add(new Triple<State, EdgeInformation, State>(newState, new InstanceEdgeMethodStartMerge(
                    "merge, is instance"), mostSimilarState));
            } else {
                edgesToAdd.add(new Triple<State, EdgeInformation, State>(newState, new InstanceEdge(
                    "merge, is instance",
                    false), mostSimilarState));
            }
        } else {
            // This is a classical merge with two parents and one child
            final State mergedState = mergeResult.getMergedState();
            //final String mergedStateBefore = mergedState.toString();
            final boolean removedAnnotation = mergedState.gc().x;
            if (expandedStateNode != null) {
                assert (!removedAnnotation) : "Removed annotation while merging child of node "
                    + expandedStateNode
                    + "\n"
                    + expandedStateNode.getState().toString()
                    + "\nMost similar node:"
                    + mostSimilarNode
                    + "\nNew state:"
                    + newState.toString()
                    + "\nMerged state:"
                    + mergedState.toString();
                //+ "\nMerged state before:"
                //+ mergedStateBefore;
            }

            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION && expandedStateNode != null) {
                final JBCMerger m = new PathMerger();
                if (m.isInstance(mergedState, mostSimilarState)) {
                    //this.dumpImage();
                    System.err.println("INSTANCE edge from merge result:"
                        + "\nMost similar node:"
                        + mostSimilarNode
                        + "\n"
                        + mostSimilarNode.getState().toString()
                        + "\nNew state:"
                        + newState.toString()
                        + "\nMerged state:"
                        + mergedState.toString());
                    if (Globals.DEBUG_COTTO) {
                        // set a breakpoint on constructor of TooExpensiveException
                        m.isInstance(newState, mostSimilarState);
                    }
                    assert (false);
                }
            }

            //add state and edges
            statesToAdd.add(mergedState);
            InstanceEdge newToMerged;
            InstanceEdge mostSimilarToMerged;
            if (methodStartMerge) {
                newToMerged = new InstanceEdgeMethodStartMerge("merge");
                mostSimilarToMerged = new InstanceEdgeMethodStartMerge("merge");
            } else {
                newToMerged = new InstanceEdge("merge", true);
                mostSimilarToMerged = new InstanceEdge("merge", true);
            }
            edgesToAdd.add(new Triple<State, EdgeInformation, State>(newState, newToMerged , mergedState));
            edgesToAdd.add(new Triple<State, EdgeInformation, State>(mostSimilarState, mostSimilarToMerged, mergedState));

            /*
             * The merge partner mostSimilarState can have a huge number
             * of successor nodes obtained by plain evaluation. Now that
             * we have merged it, we will need to re-do this anyway, so
             * the existing subgraph starting in mostSimilarState
             * becomes obsolete. We want to remove it.
             */
            nodesWithChangedSuccs.add(mostSimilarNode);

            /*
             * As we now have a new, more abstract state, try to find
             * other instances of it:
             */
            boolean needsExpansion = findInstacesAndCreateEdges(
                    mergedState, newToMerged, methodStartMerge, Collections.singleton(mostSimilarState), nodesWithChangedSuccs, edgesToAdd);
            if (needsExpansion) {
                newStatesForQueue.add(mergedState);
            }
        }

        return true;
    }

    /**
     * Does all changes needed to update a graph for the expansion of one node.
     * @param expandedStateNode the node for which we introduce new successors
     * @param statesToAdd collection of states that should be added to the graph
     * @param edgesToAdd collection of edges that should be added to the graph
     * @param newStatesForQueue collection of states that should be put into the
     * queue for further expansion
     * @param nodesWithChangedSuccs collection of nodes that get a new successor
     * (by instantiation/merge) and thus may lead to deletion of the subgraph
     * starting in them.
     * @param newMethodEndState null or a state which leads to a method end
     * ("return" opcode etc.)
     * @return null iff the changes could not be performed, otherwise a pair of
     * (i) a collection of new leafs that need to be expanded and (ii) states
     * which still need to be added to their graph (and then be expanded)
     */
    private Collection<MethodGraphWorker> performChanges(
        final Node expandedStateNode,
        final Collection<State> statesToAdd,
        final Collection<Triple<State, EdgeInformation, State>> edgesToAdd,
        final Collection<State> newStatesForQueue,
        final Collection<Node> nodesWithChangedSuccs,
        final State newMethodEndState)
    {

        this.graphLock.writeLock().lock();
        try {
            final Collection<MethodGraphWorker> tasks = new LinkedList<>();

            //Check if the changes still fit the current graph state:
            if (expandedStateNode != null) {
                if (!this.containsNode(expandedStateNode)) {
                    // nothing to do, return empty list
                    return Collections.emptySet();
                }

                if (expandedStateNode.hasInstanceSucc()) {
                    /*
                     * We already have some outgoing instance edge. Therefore, there is no need to evaluate this
                     * state.
                     */
                    return Collections.emptySet();
                }
            }

            /*
             * Check if we add an instance edge and, using that, close
             * a cycle that does not contain any evaluation.
             *
             * The node at the start of the instance edge is not part of the
             * graph, yet.
             */
            final Map<State, Node> instanceEdges = new LinkedHashMap<>();
            for (final Triple<State, EdgeInformation, State> edge : edgesToAdd) {
                if (edge.y instanceof InstanceEdge) {
                    final Node targetNode = this.getNode(edge.z);
                    if (targetNode != null) {
                        instanceEdges.put(edge.x, targetNode);
                    }
                }
            }
            for (final Triple<State, EdgeInformation, State> edge : edgesToAdd) {
                final Node targetNode = instanceEdges.get(edge.z);
                if (targetNode != null && !(edge.y instanceof EvaluationEdge)) {
                    final State from = edge.x;
                    final Node fromNode = this.getNode(from);
                    if (fromNode != null
                        && JBCGraph.hasPath(targetNode, fromNode, true, new EdgeTypeFilter(EvaluationEdge.class)))
                    {
                        // fail
                        return null;
                    }
                }
            }

            for (final Triple<State, EdgeInformation, State> edge : edgesToAdd) {
                final State stateA = edge.x;
                final Node nodeA = this.getNode(stateA);
                final State stateB = edge.z;
                final Node nodeB = this.getNode(stateB);
                /* Check if start and end of the edge are either added at the
                 * same time or are still in the graph. If not, we don't need
                 * to actually perform these changes:
                 * */
                if (!statesToAdd.contains(stateA) && !this.containsNode(nodeA)) {
                    return null;
                }
                if (!statesToAdd.contains(stateB) && !this.containsNode(nodeB)) {
                    return null;
                }
            }

            for (final Node changedNode : nodesWithChangedSuccs) {
                if (!this.containsNode(changedNode)) {
                    return null;
                }
            }

            /*
             * Add the new method end state
             */
            if (newMethodEndState != null) {
                // Do we still have this node? If not, it was already removed again.
                final Node node = this.getNode(newMethodEndState);
                if (this.containsNode(node)) {
                    tasks.addAll(this.addMethodEndStateWithLock(newMethodEndState));
                }
            }

            //Add the new states, also to our map:
            for (final State state : statesToAdd) {
                this.addState(state);
            }

            /*
             * Add the evaluation edges to the graph:
             */
            for (final Triple<State, EdgeInformation, State> newConnection : edgesToAdd) {
                if (newConnection.y instanceof EvaluationEdge) {
                    this.addEdge(newConnection.x, newConnection.y, newConnection.z);
                }
            }

            final Collection<Node> doNotDelete = new LinkedHashSet<>();
            for (final State state : statesToAdd) {
                final Node node = this.getNode(state);
                if (node != null) {
                    doNotDelete.add(node);
                }
            }

            /*
             * Unregister Method End Listeners of nodes where we introduced a new instance-successor.
             */
            for (Node node : nodesWithChangedSuccs) {
                unregisterMethodEndListeners(node, tasks);
            }

            /*
             * Delete the subgraphs of nodes where we introduced a new
             * instance-successor.
             */
            tasks.addAll(this.removeSubgraphSafely(nodesWithChangedSuccs, doNotDelete));

            /*
             * Add the non-evaluation edges to the graph:
             */
            for (final Triple<State, EdgeInformation, State> newConnection : edgesToAdd) {
                final Node nodeFrom = this.getNode(newConnection.x);
                final Node nodeTo = this.getNode(newConnection.z);
                if (!(newConnection.y instanceof EvaluationEdge) && this.containsNode(nodeFrom)) {
                    /*
                     * It can happen that we found a new instance edge target "by accident" due to standard evaluation
                     * (no merging). In this case we deleted the new instance edge target if the source of the edge was
                     * a real predecessor of the new node.
                     */
                    if (!this.containsNode(nodeTo)) {
                        this.addState(newConnection.z);
                    }
                    this.addEdge(newConnection.x, newConnection.y, newConnection.z);
                }
            }

            //Check if all of the new states are still needed:
            for (final State state : statesToAdd) {
                final Node node = this.getNode(state);
                //It was already removed: Yay.
                if (!this.containsNode(node)) {
                    continue;
                }
                final Node newStateNode = this.getNode(state);
                if (!newStateNode.hasPredecessor()) {
                    this.removeNode(newStateNode, tasks);
                }
            }

            for (final State newQueueState : newStatesForQueue) {
                final Node newQueueNode = this.getNode(newQueueState);
                if (this.containsNode(newQueueNode)) {
                    StateNodeExpander task;
                    if (tasks.isEmpty() && edgesToAdd.size() == 1) {
                        final EdgeInformation singleEdge = edgesToAdd.iterator().next().y;
                        if (singleEdge instanceof MethodStartEdge) {
                            task = new MethodStart(this, newQueueNode);
                        } else if (singleEdge instanceof CallAbstractEdge) {
                            task = new AbstractBeforeCall(this, newQueueNode);
                        } else if (singleEdge instanceof InstanceEdgeDuplicateNRIRs) {
                            task = new DuplicateNRIRs(this, newQueueNode);
                        } else if (singleEdge instanceof InstanceEdgeTryToConnect) {
                            task = new ConnectToMethodGraph(this, newQueueNode);
                        } else if (singleEdge instanceof InstanceEdgeInputReferenceChanges) {
                            // nothing to do in this graph
                            task = null;
                        } else {
                            task = new StateNodeExpanderStandard(this, newQueueNode);
                        }
                    } else {
                        boolean done = false;
                        task = null;
                        // maybe this is a state resulting out of InstanceEdgeMethodStartMerge?
                        for (final Edge inEdge : newQueueNode.getInEdges()) {
                            if (inEdge.getLabel() instanceof InstanceEdgeMethodStartMerge
                                || inEdge.getLabel() instanceof MethodStartEdge)
                            {
                                task = new MethodStart(this, newQueueNode);
                                done = true;
                                break;
                            }
                        }
                        if (!done) {
                            task = new StateNodeExpanderStandard(this, newQueueNode);
                        }
                    }
                    tasks.add(task);
                }
            }

            return tasks;
        } finally {
            this.graphLock.writeLock().unlock();
        }
    }

    /**
     * @param newState the state that should be merged
     * @param maximalMergeCosts maximal merge costs
     * @param candidates the nodes with wich we want to merge
     * @return the MergeResult with the most similar state
     */
    private JBCMergeResult findBestMergePartner(
        final State newState,
        final java.lang.Double maximalMergeCosts,
        final Collection<Node> candidates)
    {
        JBCMergeResult bestResult = null;
        final Collection<JBCMergeResult> mergeResults = this.merge(newState, candidates, maximalMergeCosts, false);
        for (final JBCMergeResult mr : mergeResults) {
            if (bestResult == null || Double.compare(bestResult.getCost(), mr.getCost()) > 0) {
                bestResult = mr;
            }
        }
        return bestResult;
    }

    /**
     * @param newEdge the edge connecting currentNode and newState
     * @param expandedStateNode the predecessor node of newState
     * @param newState the state that should be merged
     * @return the nodes with which we want to merge
     */
    private Collection<Node> findCandidateNodesForMerge(
        final State newState,
        final Node expandedStateNode,
        final EdgeInformation newEdge)
    {
        // We check all possible merge partners, trying to find a partner that is good enough
        final OpCode newOpCode = newState.getCurrentOpCode();
        final boolean withException = newState.getCallStack().getTop().hasException();
        return this.findRelatedNodes(newOpCode, withException, expandedStateNode, newEdge);
    }

    /**
     * Merge one state with many other states (or try to find instances). This
     * is done in parallel, if configured.
     * @param stateA a state
     * @param nodesForStatesB many states (with their nodes)
     * @param maximalMergeCosts the maximal cost for each merge (<= 0 for
     * "find instances" mode)
     * @param findInstances if true, we find all states in nodesForStatesB that
     * are instances of stateA. If false, we merge stateA with every state from
     * nodesForStatesB and return the best merge result.
     * @return the merge results
     */
    private Collection<JBCMergeResult> merge(
        final State stateA,
        final Collection<Node> nodesForStatesB,
        final Double maximalMergeCosts,
        final boolean findInstances)
    {
        assert (!findInstances || (maximalMergeCosts != null && maximalMergeCosts <= 0));
        final Collection<JBCMergeResult> result = new LinkedHashSet<>();
        if (this.getJBCOptions().parallelMerges && nodesForStatesB.size() > 1) {
            final Collection<MergeWorker> workers = new LinkedHashSet<>();
            for (final Node n : nodesForStatesB) {
                final MergeWorker worker;
                if (findInstances) {
                    worker = new MergeWorker(n.getState(), stateA, maximalMergeCosts);
                } else {
                    worker = new MergeWorker(stateA, n.getState(), maximalMergeCosts);
                }
                workers.add(worker);
            }

            try {
                final int queueLength = this.terminationGraph.getQueueLength();
                PrioritizableThreadPool.INSTANCE.executeNowAndWait(workers, queueLength);

                /*
                 * Make sure that there is a worker that does the merge. With acquire/release we might still run
                 * into a deadlock because the queue might be filled with other workers that wait for this worker to
                 * finish (which it cannot do if acquire blocks).
                 */
                for (final MergeWorker entry : workers) {
                    entry.waitForResult();
                    final JBCMergeResult mr = entry.getMergeResult();
                    if (mr != null) {
                        result.add(mr);
                    }
                }
            } catch (final InterruptedException e) {
                assert (false);
            }
        } else {
            if (findInstances) {
                final JBCMerger merger = new PathMerger();
                for (final Node n : nodesForStatesB) {
                    if (merger.isInstance(n.getState(), stateA)) {
                        result.add(merger.getResult());
                    }
                }
            } else {
                final JBCMerger merger = new PathMerger(stateA, maximalMergeCosts);
                for (final Node n : nodesForStatesB) {
                    if (merger.merge(n.getState())) {
                        result.add(merger.getResult());
                    }
                }
            }
        }
        return result;
    }

    /**
     * Check the graph if it already contains states that are instances of this
     * new state. Also detects equal nodes (where both this instance other and other instance this holds)
     * @param someState some state which is a candidate for incoming instance
     * edges (i.e. obtained by either merging or evaluation)
     * @param label the label of the edge leading to this state
     * @return a list of states that are equal to the new state, and a list of state that are an instance of new state.
     */
    private Pair<Collection<Node>, Collection<Node>> findInstancesOf(final State someState, final EdgeInformation label) {
        if (!this.getJBCOptions().incomingInstanceFinder || someState.getReferences().isEmpty()) {
            return new Pair<>(Collections.emptyList(), Collections.emptyList());
        }

        final Collection<Node> equal = new LinkedList<>();
        final Collection<Node> instance = new LinkedList<>();
        final OpCode opCode = someState.getCurrentOpCode();
        final Collection<Node> relatedNodes =
                this.findRelatedNodes(opCode, someState.getCallStack().getTop().hasException(), null, label);
        final Map<State, Node> nodeMap = relatedNodes.stream().collect(toMap(x-> x.getState(), x->x));
        final Collection<JBCMergeResult> mergeResults =
                this.merge(someState, relatedNodes, 0., true);
        for (final JBCMergeResult mr : mergeResults) {
            assert (mr.partnerEqualsMergedState());
            final Node node = nodeMap.get(mr.getHeapPositionsA().getState());
            assert (node != null);
            if (mr.getCost()<= 0) {
                equal.add(node);
            } else {
                instance.add(node);
            }
        }
        return new Pair<>(equal, instance);
    }

    /**
     * Uses {@link MethodGraph#findInstancesOf(State, EdgeInformation)} to find instances of state, and then creates instance edges from them to state.
     * In case we find any equal states, we will create an instance edge from state to the equal node.
     * That way the node created for the state will not need to be expanded further, this is signalled by the return value and should be done by the caller.
     * @param state state which is a candidate for incoming instance edges (i.e. obtained by either merging or evaluation)
     * @param labelToState the label of the edge leading to state
     * @param instanceEdgeMethodStartMerge whether InstanceEdgeMethodStartMerge or normal InstanceEdge should be used
     * @param ignore nodes to not create edges to
     * @param nodesWithChangedSuccs collection of nodes that get a new successor
     * (by instantiation/merge) and thus may lead to deletion of the subgraph
     * @param edgesToAdd collection of edges that should be added to the graph.
     * @return whether the state needs further expansion
     */
    private boolean findInstacesAndCreateEdges(
            final State state,
            final EdgeInformation labelToState,
            final boolean instanceEdgeMethodStartMerge,
            final Collection<State> ignore,
            final Collection<Node> nodesWithChangedSuccs,
            final Collection<Triple<State, EdgeInformation, State>> edgesToAdd) {
        Pair<Collection<Node>,Collection<Node>> equalAndInstance = this.findInstancesOf(state, labelToState);
        for (final Node instance : equalAndInstance.y) {
            if (ignore.contains(instance.getState()))
                continue;
            EdgeInformation label;
            if (instanceEdgeMethodStartMerge) {
                label = new InstanceEdgeMethodStartMerge("findInstanceOf");
            } else {
                label = new InstanceEdge("findInstanceOf", false);
            }
            edgesToAdd.add(new Triple<State, EdgeInformation, State>(instance.getState(), label, state));
            nodesWithChangedSuccs.add(instance);
        }
        for (final Node equal : equalAndInstance.x) {
            if (ignore.contains(equal.getState()))
                continue;
            //we were lucky and found a node that is equal to ours, add an instance edge from newState to that one, and remove newState from the queue
            EdgeInformation label;
            if (instanceEdgeMethodStartMerge) {
                label = new InstanceEdgeMethodStartMerge("findEqual");
            } else {
                label = new InstanceEdge("findEqual", false);
            }
            edgesToAdd.add(new Triple<State, EdgeInformation, State>(state, label, equal.getState()));
            return false;
        }
        return true;
    }

    /**
     * Do some checks.
     */
    public void check() {
        if (!Globals.DEBUG_CHRISTIAN && !Globals.DEBUG_FKUERTEN) {
            return;
        }
        this.graphLock.readLock().lock();
        try {
            final RefineReversible refRev = new RefineReversible(this);
            if (!refRev.check()) {
                final String prefix = this.dumpImage();
                assert (false) : "RefineReversible failed: " + refRev + " See dump in " + prefix;
            }

            final InstanceEdgeUpwards iCheck = new InstanceEdgeUpwards(this);
            if (!iCheck.check()) {
                final String prefix = this.dumpImage();
                assert (false) : "InstanceEdgeUpwards failed: " + iCheck + " See dump in " + prefix;
            }

            final OneRootOnly rootCheck = new OneRootOnly(this);
            if (!rootCheck.check()) {
                final String prefix = this.dumpImage();
                assert (false) : "OneRootOnly failed: " + rootCheck + " See dump in " + prefix;
            }

            if (Globals.DEBUG_CHRISTIAN) {
                final OutEdgeTypes outEdgeTypes = new OutEdgeTypes(this);
                if (!outEdgeTypes.check()) {
                    final String prefix = this.dumpImage();
                    assert (false) : "OutEdgeTypes failed: " + outEdgeTypes + " See dump in " + prefix;
                }
            }

            if (Globals.DEBUG_FKUERTEN) {
                final MethodStartStructure methodStartStructure = new MethodStartStructure(this);
                if (!methodStartStructure.check()) {
                    final String prefix = this.dumpImage();
                    assert false : "Structure near method start is incorrect: "
                        + methodStartStructure.toString()
                        + " See dump in "
                        + prefix;
                }
            }
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * Dump the graph to disk and return the prefix of the dump file.
     * @return prefix of the dump file
     */
    public String dumpImage() {
        JBCOptions jbcOptions = this.terminationGraph.getJBCOptions();
        if (!jbcOptions.pathToGraphDumpDirectory().isPresent()
                || (!jbcOptions.dumpIntermediateTerminationGraphs() && !this.finished))
        {
            return null;
        }
        final String path = jbcOptions.pathToGraphDumpDirectory().get();
        final File phtml = new File(path);
        if (!phtml.exists()) {
            return null;
        }
        final String name = "methodgraph_" + this.parsedMethod.getName().replace(">", "");
        final String latest = "latest_" + this.parsedMethod.getName() + ".svg";
        final long nanos = System.nanoTime();
        final String prefix = path + "/" + name + nanos;
        try {
            try (BufferedWriter bw = new BufferedWriter(new FileWriter(prefix + ".txt"))) {
                this.toDOT(bw);
            }

            if (Globals.DEBUG_COTTO) {
                Runtime.getRuntime().exec("rm " + path + "/" + latest);
                Runtime.getRuntime().exec("ln -s " + prefix + ".svg " + path + "/" + latest);
            }
            return prefix;
        } catch (final IOException e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * @param n a node
     * @return true if there is a (non-hidden) predecessor of n
     */
    public boolean hasPredecessor(final Node n) {
        assert (this.containsNode(n));
        return n.equals(startNode) || !n.getInEdges().isEmpty();
    }

    /**
     * Find nodes that could be related to the given state. The policy here is
     * that only nodes are returned that are allowed to be the target of an
     * INSTANCE edge (if the content is OK, too).
     * @param opc the current opcode
     * @param withException true if the given state throws an exception
     * @param predecessor the current node (predecessor of the node to be added)
     * @param e the edge that should be created
     * @return a collection of nodes that are considered to be related, so that
     * it would be a good idea to draw an INSTANCE edge to one of these nodes
     */
    private Collection<Node> findRelatedNodes(
        final OpCode opc,
        final boolean withException,
        final Node predecessor,
        final EdgeInformation e)
    {
        final Collection<Node> result;

        this.graphLock.readLock().lock();
        try {
            if (opc == null) {
                return Collections.emptyList();
            }
            Collection<Node> interestingNodes;
            if (e instanceof MethodSkipEdge) {
                interestingNodes = new LinkedHashSet<>();
                for (final Edge outEdge : predecessor.getOutEdges()) {
                    if (outEdge.getLabel() instanceof MethodSkipEdge) {
                        final Node endNode = outEdge.getEnd();
                        final State endState = endNode.getState();
                        if (endState.getCurrentOpCode().equals(opc)
                            && endState.getCurrentStackFrame().hasException() == withException)
                        {
                            Node endOfInstance = endNode;
                            boolean found = true;
                            while (found) {
                                found = false;
                                for (final Edge instanceEdge : endOfInstance.getOutEdges()) {
                                    if (instanceEdge.getLabel() instanceof InstanceEdge)
                                    {
                                        endOfInstance = instanceEdge.getEnd();
                                        found = true;
                                    }
                                }
                            }
                            interestingNodes.add(endOfInstance);
                        }
                    }
                }
                result = interestingNodes.stream()
                        .filter(node -> !node.hasInstanceSuccIn(interestingNodes))
                        .collect(toList());

            } else {
                final Pair<OpCode, Boolean> pair = new Pair<>(opc, withException);
                interestingNodes = this.nodesForOpcode.getNotNull(pair);
                result = interestingNodes.stream()
                        .filter(node -> !node.hasRefineOrSplitPredIn(interestingNodes))
                        .filter(node -> !node.hasCallAbstractSuccIn(interestingNodes))
                        .filter(node -> !node.hasInstanceSuccIn(interestingNodes))
                        .collect(toList());
            }

            /*
             * If the predecessor is connected using an EVAL edge,
             * everything is fine. In all other cases we must take care that
             * we do not consider nodes as related if (by adding an INSTANCE
             * edge) we can create a loop without a single EVAL edge.
             */
            if (predecessor != null && !(e instanceof EvaluationEdge)) {
                result.removeIf(node -> hasPath(node, predecessor, true, new EdgeTypeFilter(EvaluationEdge.class)));
            }
        } finally {
            this.graphLock.readLock().unlock();
        }

        return result;
    }

    /**
     * Removes everything in the subgraph starting at one of the nodes in
     * startNode (but <b>not</b> one of them) which is not reachable by another
     * part of the non-hidden graph.
     * @param startNodes nodes starting subgraphs to remove.
     * @param doNotDelete do not delete these nodes
     * @return additional workers that need to be executed
     */
    private Collection<MethodGraphWorker> removeSubgraphSafely(
        final Collection<Node> startNodes,
        final Collection<Node> doNotDelete)
    {
        if (startNodes.isEmpty()) {
            return Collections.emptySet();
        }

        graphLock.writeLock().lock();
        try {
            // Algorithm to safely remove the sub-graph starting in the node a:

            // - Compute Set R = reachableNodes(a) of nodes reachable by a
            // - for n in R:
            //     if incomingEdges(n) \not \subseteq R:
            //        R := R \setminus ({n} \cup children(n))
            // - Remove R from graph
            /*
             * Translation: Do not remove nodes that are reachable by some "foreign"
             * node
             */

            // get all reachable nodes:
            final Set<Node> toRemove = JBCGraph.determineReachableNodes(startNodes);
            toRemove.removeAll(startNodes);
            toRemove.remove(this.startNode);

            // filter out those that are needed from somewhere else:
            final Set<Node> changes = new LinkedHashSet<>();

            final EdgeFilter filter = new DontCrossNodesEdgeFilter(startNodes, this);

            final Collection<Node> boundaryNodes = new LinkedHashSet<>();

            do {
                toRemove.removeAll(changes);
                changes.clear();
                for (final Node n : toRemove) {
                    // get a working copy of all incoming edges:
                    for (final Edge edge : n.getInEdges()) {
                        final Node edgeStartNode = edge.getStart();
                        // we don't care about edges from our startNodes:
                        if (startNodes.contains(edgeStartNode)) {
                            continue;
                        }
                        if (!toRemove.contains(edgeStartNode)) {
                            /*
                             * there is some external and non-hidden node pointing to
                             * this node, so it would be very bad to delete this node
                             */
                            final Collection<Node> stillNeededNodes = Collections.singleton(n);
                            changes.addAll(JBCGraph.determineReachableNodes(stillNeededNodes, filter));
                        }
                    }
                }
            } while (!changes.isEmpty());

            // find all nodes where we stopped deletion
            for (final Node n : toRemove) {
                for (final Edge outEdge : n.getOutEdges()) {
                    final Node out = outEdge.getEnd();
                    boundaryNodes.add(out);
                }
            }
            toRemove.removeAll(doNotDelete);
            boundaryNodes.removeAll(toRemove);

            // remove everything that is left:
            final LinkedHashSet<MethodGraphWorker> result = new LinkedHashSet<>();
            for (final Node n : toRemove) {
                removeNode(n, result);
            }

            final Collection<Edge> toDelete = new LinkedHashSet<>();
            /*
             * If a direct successor of a node with a changed successor is not
             * deleted (because it is needed by another part of the graph), we
             * still have the edge connecting these two nodes. We need to remove
             * it explicitly:
             */
            for (final Node changedNode : startNodes) {
                for (final Edge outEdge : changedNode.getOutEdges()) {
                    if (!toRemove.contains(outEdge.getEnd())) {
                        toDelete.add(outEdge);
                    }
                }

                //If the changed node isn't needed anymore, remove it:
                if (!this.hasPredecessor(changedNode)) {
                    removeNode(changedNode, result);
                }
            }

            for (final Edge edge : toDelete) {
                removeEdge(edge);
            }
            return result;
        } finally {
            graphLock.writeLock().unlock();
        }
    }

    /**
     * @return a nice string that can be used to generate an even nicer dotty
     * graph.
     */
    public String toDOT() {
        try {
            return toDOT(new StringBuilder()).toString();
        } catch (IOException e) {
            //never happens for Stringbuilder
            return null;
        }
    }

    /**
     * @param sb an Appendable to append the dot String to
     * @return the Appendable
     * @throws IOException
     */
    public Appendable toDOT(Appendable a) throws IOException {
        a.append("digraph dp_graph {\n"
                + "graph [mindist=0.3,nodesep=0.05,concentrate=true,ranksep=0.05];\n"
                + "node [shape=rectangle,fontsize=10];\n"
                + "edge [labeldistance=3,headclip=true,fontsize=8];\n");

        this.toDOTNodesAndEdges(a);
        a.append("}\n");
        return a;
    }

    /**
     * Fill the string builder with nodes and rules
     * @param t a string builder
     * @throws IOException
     */
    public void toDOTNodesAndEdges(final Appendable t) throws IOException {
        /*
         * We need a read lock for dumping or the dump might be inconsistent
         * In addition, ConcurrentModificationExceptions might get thrown.
         */
        this.graphLock.readLock().lock();
        try {
            GraphToDot.toDot(this, t, null);
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * Export our knowledge from the graph.
     * @param o export util
     * @return textual representation of the graph
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        final int nodeNumber = this.getNodeNumber();
        final int sccNumber = this.getSCCs().size();
        sb.append("Graph of " + nodeNumber + " nodes with " + sccNumber + " SCC");
        if (sccNumber == 1) {
            sb.append(".");
        } else {
            sb.append("s.");
        }
        return sb.toString();
    }

    /**
     * We assume that the graph is already locked. This method should only be
     * called if this is the case, for example from
     * {@link #performChanges(Node, Collection, Collection, Collection, Collection, State)}
     * @param newMethodEnd a new method end
     * @return new nodes, which should be added to the graphs and queue
     */
    private Collection<MethodGraphWorker> addMethodEndStateWithLock(final State newMethodEnd) {
        if (Globals.useAssertions) {
            assert (!this.methodEndStates.contains(newMethodEnd));
            assert this.graphLock.writeLock().isHeldByCurrentThread();
        }
        this.methodEndStates.add(newMethodEnd);

        final Collection<MethodGraphWorker> result = new ArrayList<>(methodEndListeners.size());
        for (final MethodEndListener l : new ArrayList<>(this.methodEndListeners)) {
            /*
             * Adding the new method end directly to its graph requires a write lock.
             * Unfortunately, calculating the new method end requires already a read lock.
             * Hence we defer the calculation of the new method end until later.
             */
            final MethodEndCreator task = new MethodEndCreator(this, l, newMethodEnd);
            result.add(task);
        }
        return result;
    }

    /**
     * Find out if construction of this graph is finished.
     */
    private void checkFinished() {
        if (!this.getJBCOptions().retainFinishedGraphs || this.finished) {
            return;
        }
        // a worker object for this graph was created, but did not finish, yet
        if (this.waitingWorkers.intValue() > 1) {
            return;
        }
        // is there a graph that could provide a new return state for a call state in this graph?
        for (final MethodGraph mg : this.getTerminationGraph().getMethodGraphs()) {
            /*
             * We know there is no worker for this graph, so if only this graph can create new return states for
             * listeners in this graph, we will not get any.
             */
            if (this.equals(mg)) {
                continue;
            }
            // we will not get a new return state from a finished graph
            if (mg.finished) {
                continue;
            }
            for (final MethodEndListener mel : mg.methodEndListeners) {
                if (this.equals(mel.getMethodGraph())) {
                    return;
                }
            }
        }
        this.finished = true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<State> addMethodEndListener(final MethodEndListener l) {
        Set<State> result;
        this.graphLock.writeLock().lock();
        try {
            this.methodEndListeners.add(l);
            result = new LinkedHashSet<>(this.methodEndStates);
        } finally {
            this.graphLock.writeLock().unlock();
        }
        return result;
    }

    /**
     * Returns the start node of this method graph, i.e, the single node without
     * any predecessor.
     * @return start node
     */
    public Node getStartNode() {
        return this.startNode;
    }

    /**
     * This is the callback reaction method for new ends in some graph. Adds a
     * successor corresponding to <code>endingState</code> to
     * <code>callingNode</code>.
     * @param endingGraph graph containing the node that returns
     * @param endingState end state of <code>endingGraph</code>
     * @param callingNode a node in <code>this</code> graph with the top
     * stackframe at the start of the method ending in <code>endingState</code>.
     * @return the state to add, must be added to the graph and queue later
     * (null if nothing needs to be done)
     * @see MethodEndListener#newMethodEnd(MethodGraph, State)
     */
    public Collection<MethodGraphWorker> newMethodEnd(
        final MethodGraph endingGraph,
        final State endingState,
        final Node callingNode)
    {
        return MethodEndHelper.newMethodEnd(endingGraph, endingState, this, callingNode);
    }

    /**
     * Creates a {@link MethodEndListener} for this graph and the specified
     * node.
     * @param invokingNode a node in this graph
     * @return a {@link MethodEndListener} for this graph and node
     */
    public MethodEndListener createListener(final Node invokingNode) {
        if (Globals.useAssertions) {
            assert invokingNode.getState().getCurrentOpCode().getPos() == 0;
            /*
             * If the graph deletes this node, we will still create a listener.
             * (Checking whether the graph contains the node would require a
             * readlock, which might cause a deadlock.)
             * This check will be deferred to the time when the listener is called.
             */
        }
        return new MethodEndListener(invokingNode, this);
    }

    /**
     * @return the method this graph is built for
     */
    public IMethod getParsedMethod() {
        return this.parsedMethod;
    }

    /**
     * @return the graph lock
     */
    public ReentrantReadWriteLock getGraphLock() {
        return this.graphLock;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.startNode.toString();
    }

    /**
     * @return the method end listeners
     */
    public Collection<MethodEndListener> getMethodEndListeners() {
        this.graphLock.readLock().lock();
        try {
            return new ArrayList<>(this.methodEndListeners);
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * @return the method end states;
     */
    public Collection<State> getMethodEndStates() {
        this.graphLock.readLock().lock();
        try {
            return new ArrayList<>(this.methodEndStates);
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * Remove the method end listeners with the stored node
     * @param listeningNode a node
     * @return true if some listener was removed
     */
    public boolean removeMethodEndListener(final Node listeningNode) {
        this.graphLock.writeLock().lock();
        try {
            for (final MethodEndListener l : this.methodEndListeners) {
                if (l.getNode().equals(listeningNode)) {
                    this.methodEndListeners.remove(l);
                    return true;
                }
            }
        } finally {
            this.graphLock.writeLock().unlock();
        }
        return false;
    }

    /**
     * @return the termination graph
     */
    public TerminationGraph getTerminationGraph() {
        return this.terminationGraph;
    }

    /**
     * @return the set of all hidden nodes in this graph.
     */
    public Set<Node> getHiddenNodes() {
        graphLock.readLock().lock();
        try {
        return new LinkedHashSet<>(hidden);
        } finally {
            graphLock.readLock().unlock();
        }
    }

    /**
     * @return the set of all hidden edges in this graph.
     */
    public Set<Edge> getHiddenEdges() {
        final Set<Edge> res = new LinkedHashSet<>();
        graphLock.readLock().lock();
        try {
            for (final Node n : hidden) {
                res.addAll(n.getHiddenInEdges());
                res.addAll(n.getHiddenOutEdges());
            }
            return res;
        } finally {
            graphLock.readLock().unlock();
        }
    }

    /**
     * @return the set of all debug edges in this graph.
     */
    public Set<Edge> getDebugEdges() {
        final Set<Edge> res = getHiddenEdges();
        res.removeIf(e -> !(e.getLabel() instanceof DebugEdge));
        return res;
    }

    /**
     * To create a finite termination graph, we may need to retain states
     * resulting out of a return from some invoked method, even though the
     * corresponding return state does not exist anymore. These are not needed
     * anymore when the construction is finished and are deleted here.
     */
    public void removeUselessReturns() {
        assert(graphLock.isWriteLockedByCurrentThread());
        final Collection<Edge> remove = new ArrayList<>();
        for (final Edge edge : this.getEdges()) {
            final EdgeInformation label = edge.getLabel();
            if (label instanceof MethodSkipEdge) {
                final MethodSkipEdge mse = (MethodSkipEdge) label;
                if (mse.getGraph() == null || !mse.getGraph().containsNode(mse.getNode())) {
                    remove.add(edge);
                }
            }
        }
        final Collection<Node> edgeEnds = new ArrayList<>();
        for (final Edge removeMe : remove) {
            removeEdge(removeMe);
            if (removeMe.getEnd().getInEdges().isEmpty()) {
                edgeEnds.add(removeMe.getEnd());
            }
        }

        this.removeSubgraphSafely(edgeEnds, Collections.emptyList());
        for (Node n : edgeEnds)
            this.removeNodeWithLocks(n);
    }

    /**
     * @return the options provided to the processor
     */
    public JBCOptions getJBCOptions() {
        return this.getTerminationGraph().getJBCOptions();
    }

    /**
     * @param newEdge the edge that may be used to connect the new state
     * @param newState the new state
     * @param src the source of the edge
     * @return an Integer indicating how much a merge should maximally cost. If
     * NULL, we *have* to merge.
     */
    public Double getMaximalAllowedMergeCosts(final EdgeInformation newEdge, final State newState, final Node src) {
        if (!(newEdge instanceof EvaluationEdge)
            && !(newEdge instanceof CallAbstractEdge)
            && !(newEdge instanceof MethodSkipEdge))
        {
            return 0.;
        }
        if (newEdge instanceof CLInitDoneEdge) {
            return 0.;
        }

        this.graphLock.readLock().lock();
        try {
            final OpCode newOpCode = newState.getCurrentOpCode();
            final boolean hasException = newState.getCurrentStackFrame().hasException();

            /*
             * Are we dealing with a return state we already saw, just with
             * different values? If so, merge!
             */
            if (newEdge instanceof MethodSkipEdge) {
                for (final Edge outEdge : src.getOutEdges()) {
                    if (outEdge.getLabel() instanceof MethodSkipEdge) {
                        final Node endNode = outEdge.getEnd();
                        final State endState = endNode.getState();
                        if (endState.getCurrentOpCode().equals(newOpCode)
                            && endState.getCurrentStackFrame().hasException() == hasException)
                        {
                            try {
                                JBCMerger.JBCMergerSkeleton.mergeInitialization(newState, endState, null);
                                return null;
                            } catch (final TooExpensiveException e) {
                                continue;
                            }
                        }
                    }
                }
                return 0.;
            }

            //are there any merge candidates?
            if (nodesForOpcode.getNotNull(new Pair<>(newOpCode, hasException)).isEmpty()) {
                return 0.;
            }

            Collection<State> states;
            //only enforce the post-loop merge if we evaluated, the last opcode was a jump and we actually jumped
            OpCode srcOpCode = src.getState().getCurrentOpCode();
            if (newEdge instanceof EvaluationEdge
                 && srcOpCode instanceof Branch
                 && ((Branch)srcOpCode).getBranchOffset() < 0
                 && ((Branch)srcOpCode).getBranchTarget().equals(newOpCode))
            {
                //first find all nodes that could belong to the same loop, stop when leaving the method or when classloading
                Set<Node> candidates = determineReachingNodes(
                        Collections.singleton(src),
                        new CombinationEdgeFilter(
                                new StayInMethodEdgeFilter(newState, true),
                                RefinementDoNotMergeFilter.INSTANCE,
                                NoClassLoadingEdgeFilter.INSTANCE));
                //second filter so we only have nodes with the correct OpCode and the same (non null) Root Positions
                Set<RootPosition> newRoots = new HashSet<>(HeapPositions.collectRootPositions(newState));
                newRoots.removeIf(pos -> pos.getFromState(newState).isNULLRef());
                Set<Node> nodes = candidates.stream()
                        .filter(node -> node.getState().getCurrentOpCode().equals(newOpCode))
                        .filter(node -> {
                            Set<RootPosition> oldRoots = new HashSet<>(HeapPositions.collectRootPositions(node.getState()));
                            oldRoots.removeIf(pos -> pos.getFromState(node.getState()).isNULLRef());
                            return newRoots.equals(oldRoots);
                        })
                        .collect(toSet());
                //last remove all nodes that have a refine predecessor or instance successor
                states = nodes.stream()
                        .filter(node -> !node.hasRefineOrSplitPredIn(nodes)
                                && !node.hasInstanceSuccIn(nodes))
                        .map(Node::getState)
                        .collect(toList());
            } else {
                states = Collections.emptyList();
            }

            int loopCount = states.size();
            if (loopCount >= this.getJBCOptions().loopMaximalIterations()) {
                return null;
            }

            /*
             * If the resulting state needs to be refined, we search for
             * other states at the same program position which were derived
             * from a common ancestor.
             * If that is the case and it looks like these branches have been
             * computed in parallel for some time now, we want to try to merge
             * them, even if this loses some information.
             */
            if (newEdge instanceof EvaluationEdge
                    && this.getJBCOptions().tryParallelPathMerging
                    && !hasException)
            {
                boolean needsRefine = newOpCode.needsRefine(newState);
                if (needsRefine) {
                    final Collection<Node> relatedNodes = this.findRelatedNodes(newOpCode, hasException, src, newEdge);

                    /* We are ignoring instance edges here to correctly handle
                     * cycles in the graph:
                     */
                    final Collection<Node> expandedNodePredecessors =
                            JBCGraph.determineReachingNodes(Collections.singleton(src), new EdgeTypeFilter(
                                    InstanceEdge.class));

                    /*
                     * Store the maximal number of evaluation steps that
                     * separate a possible partner from the common ancestor.
                     */
                    int maxPredEvalDist = 0;
                    for (final Node n : relatedNodes) {
                        final Set<Integer> seenNodes = new LinkedHashSet<>();
                        final Queue<Pair<Node, Integer>> nodesToVisit = new LinkedList<>();

                        /*
                         * Do a breadth-first search to find the first
                         * ancestor that is a predecessor of the currently
                         * expanded node.
                         */
                        nodesToVisit.add(new Pair<>(n, 0));
                        while (!nodesToVisit.isEmpty()) {
                            final Pair<Node, Integer> t = nodesToVisit.remove();
                            final Node curNode = t.x;
                            final int curDist = t.y;
                            if (!seenNodes.add(curNode.getNodeNumber())) {
                                continue;
                            }
                            if (expandedNodePredecessors.contains(curNode)) {
                                if (maxPredEvalDist < curDist) {
                                    maxPredEvalDist = curDist;
                                }
                                break;
                            }

                            for (final Edge e : curNode.getInEdges()) {
                                final Node inNode = e.getStart();
                                if (e.getLabel() instanceof EvaluationEdge) {
                                    nodesToVisit.add(new Pair<>(inNode, curDist + 1));
                                } else {
                                    nodesToVisit.add(new Pair<>(inNode, curDist));
                                }
                            }
                        }

                        //Now we need to decide how much a merge should maximally cost:
                        return Math.pow(Math.E, 1 + relatedNodes.size() * maxPredEvalDist / 100);
                    }
                }
            }

            if (loopCount <= 1) {
                return 0.;
            }

            return this.getJBCOptions().loopMergeCostBase
                + (loopCount - 1)
                * this.getJBCOptions().loopMergeCostChange;

        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * @param newStartState the new start state
     * @param nodeNr the number of the node that causes the new start node to
     * exist
     */
    public void newStartState(final State newStartState, final int nodeNr) {
        this.graphLock.writeLock().lock();
        try {
            final Node oldStart = this.startNode;
            this.startNode = new Node(newStartState);
            this.addNode(this.startNode);
            this.addEdge(oldStart, new NewStartStateEdge(nodeNr), this.startNode);
            this.nonTermQueue.clear();
            for (Node node : new ArrayList<>(this.getNodes())) {
                if (node == this.startNode)
                    continue;
                this.removeNodeWithLocks(node);
            }
            final Pair<OpCode, Boolean> pair =
                new Pair<>(oldStart.getState().getCurrentOpCode(), oldStart
                    .getState()
                    .getCurrentStackFrame()
                    .hasException());
            this.nodesForOpcode.removeFromCollection(pair, oldStart);
            this.nodesForOpcode.add(pair, this.startNode);
            if (Globals.useAssertions) {
                assert this.getNodes().size() == 1;
                assert this.methodEndStates.isEmpty();
                assert this.nodesForOpcode.allValues().size() == 1;
            }
        } finally {
            this.graphLock.writeLock().unlock();
        }
    }

    /**
     * @return the threading policy (queue) for this method graph
     */
    public ThreadingPolicy getThreadingPolicy() {
        return this.policy;
    }

    /**
     * This method is called whenever a worker for this method graph has been executed. The number of waiting workers is
     * decreased by one.
     * @throws AbortionException when the aborter kicks in
     */
    public void workerExecution() throws AbortionException {
        final int remaining = this.waitingWorkers.decrementAndGet();
        if (remaining != 0) {
            return;
        }
        if (!this.delayedMerges.isEmpty()) {
            final Collection<MethodGraphWorker> res = new LinkedHashSet<>();
            final Collection<OpCode> remove = new LinkedHashSet<>();
            final Collection<Node> nodesWithChangedSuccs = new LinkedHashSet<>();
            final Collection<Node> newNodes = new LinkedHashSet<>();

            for (final Entry<OpCode, Pair<State, Collection<Triple<Node, EdgeInformation, State>>>> entry : this.delayedMerges
                .entrySet())
            {

                final State mergedState = entry.getValue().x;

                boolean addedMergedState = false;
                // first round: add the delayed states and add the resulting merged state once
                for (final Triple<Node, EdgeInformation, State> innerEntry : entry.getValue().y) {
                    final Collection<State> statesToAdd = new LinkedHashSet<>();
                    if (!addedMergedState) {
                        statesToAdd.add(mergedState);
                    }
                    statesToAdd.add(innerEntry.z);

                    final Collection<Triple<State, EdgeInformation, State>> edgesToAdd = new LinkedHashSet<>();
                    edgesToAdd.add(new Triple<>(innerEntry.x.getState(), innerEntry.y, innerEntry.z));

                    final Collection<State> newStatesForQueue = new LinkedHashSet<>();

                    if (innerEntry.z != mergedState) {
                        final EdgeInformation instanceEdge = new InstanceEdge("delayed merge", true);
                        edgesToAdd.add(new Triple<>(innerEntry.z, instanceEdge, mergedState));
                    }

                    Collection<MethodGraphWorker> newTasks = null;
                    do {
                        newTasks =
                            this.performChanges(
                                innerEntry.x,
                                statesToAdd,
                                edgesToAdd,
                                newStatesForQueue,
                                nodesWithChangedSuccs,
                                null);
                        if (JBCOptions.DEBUG_DELAYMERGE && newTasks == null) {
                            System.out.println("repeating (delay 1)");
                        }
                    } while (newTasks == null);

                    final Node mergedStateNode = this.getNode(mergedState);
                    if (this.containsNode(mergedStateNode)) {
                        addedMergedState = true;
                    }
                    addedMergedState = false;

                    for (final State state : statesToAdd) {
                        newNodes.add(this.getNode(state));
                    }

                    res.addAll(newTasks);
                }

                /*
                 * second round: take care that the resulting merge state is merged with the rest of the graph and work is
                 * continued on it
                 */
                for (final Triple<Node, EdgeInformation, State> innerEntry : entry.getValue().y) {
                    if (innerEntry.y instanceof EvaluationEdge) {
                        final Collection<Node> candidates =
                            this.findCandidateNodesForMerge(innerEntry.z, innerEntry.x, innerEntry.y);

                        // we want to merge with the "old world", so we remove everything we added in this step
                        candidates.removeAll(newNodes);

                        final JBCMergeResult bestResult = this.findBestMergePartner(mergedState, null, candidates);
                        if (bestResult != null) {
                            final Collection<State> statesToAdd = new LinkedHashSet<>();
                            final Collection<Triple<State, EdgeInformation, State>> edgesToAdd = new LinkedHashSet<>();
                            final Collection<State> newStatesForQueue = new LinkedHashSet<>();

                            this.handleMergeResult(
                                mergedState,
                                bestResult,
                                innerEntry.x,
                                statesToAdd,
                                edgesToAdd,
                                newStatesForQueue,
                                nodesWithChangedSuccs,
                                false);

                            Collection<MethodGraphWorker> newTasks = null;
                            do {
                                newTasks =
                                    this.performChanges(
                                        innerEntry.x,
                                        statesToAdd,
                                        edgesToAdd,
                                        newStatesForQueue,
                                        nodesWithChangedSuccs,
                                        null);
                                if (JBCOptions.DEBUG_DELAYMERGE && newTasks == null) {
                                    System.out.println("repeating (delay 2)");
                                }
                            } while (newTasks == null);
                            res.addAll(newTasks);

                            break;
                        }
                    }
                }

                remove.add(entry.getKey());

                // only handle a single delayed merge now
                if (!res.isEmpty()) {
                    break;
                }
            }

            for (final OpCode removeMe : remove) {
                this.delayedMerges.remove(removeMe);
            }
            this.terminationGraph.addJobs(res);
        }
        this.checkFinished();
    }

    /**
     * This method is called whenever a new worker for this method graph is created. The number of waiting workers is
     * increased by one.
     */
    public void newWorker() {
        this.waitingWorkers.incrementAndGet();
    }

    /**
     * Remember the given worker and run it as soon as all graphs are finished.
     * @param worker a NonTerm worker
     */
    public void queueNonTermWorker(final NonTermWorker worker) {
        this.nonTermQueue.add(worker);
    }

    /**
     * Add the jobs that were queued before
     * @param queue the queue for the jobs
     * @throws AbortionException when the aborter kicks in
     */
    public void runNonTermWorkers(final QueueManager<MethodGraphWorker> queue) throws AbortionException {
        this.graphLock.writeLock().lock();
        for (final MethodGraphWorker worker : this.nonTermQueue) {
            queue.add(worker);
        }
        this.nonTermQueue.clear();
        this.graphLock.writeLock().unlock();
    }

    /**
     * @return true if construction of this method graph is finished
     */
    public boolean isFinished() {
        return this.finished;
    }

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Start", this.startNode.getNodeNumber());

        final JSONArray nodes = new JSONArray();
        for (Node n : this.getNodes()) {
            final JSONObject node = new JSONObject();
            node.put("ID", n.getNodeNumber());
            node.put("State", n.getState().toJSON());
    	    nodes.put(node);
        }
        res.put("Nodes", nodes);

        final JSONArray edges = new JSONArray();
        for (Edge e : this.getEdges()) {
            final JSONObject edge = new JSONObject();
            edge.put("Source", e.getStart().getNodeNumber());
            edge.put("Target", e.getEnd().getNodeNumber());
            if (!(e.getLabel() instanceof InitializationStateChange)) {
                edge.put("Label", e.getLabel().toJSON());
            }
            edges.put(edge);
        }
        res.put("Edges", edges);

        return res;
    }
}
