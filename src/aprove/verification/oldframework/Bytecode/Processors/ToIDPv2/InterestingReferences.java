package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class holds a mapping from states in the FIGraph to abstract variable
 * references we consider interesting. "Interesting" in this case means "may be
 * useful for termination" analysis. Uninteresting references are such that are
 * never read (used for a comparison, field access) in a certain
 * SCC. The computation of interesting references is also done in this class.
 *
 * @author Christian von Essen
 */
public class InterestingReferences {
    /**
     * References for each state of an FIGraph
     */
    private final CollectionMap<State, AbstractVariableReference> refs =
        new CollectionMap<>();

    /**
     * Remember the references for which we already investigated all references
     * on the path to the root.
     */
    private final CollectionMap<State, AbstractVariableReference> checkedToRoot =
        new CollectionMap<>();

    /**
     * List of static fields changed in the considered subgraph.
     */
    private final Set<Pair<ClassName, String>> changedStaticFields =
        new LinkedHashSet<>();

    /**
     * Cache the heap positions for the states.
     */
    private final Map<State, HeapPositions> heapPositionsCache;

    /**
     * Cache the reference sets for the states.
     */
    private final Map<State, Collection<AbstractVariableReference>> allReferencesCache;

    /**
     * Create a new object and do the interesting reference analysis.
     * @param graph Some SCC in a FIGraph.
     * @param paperMode iff true, interesting references will be computed as
     * described in the nontermination paper.
     * @param aborter the aborter
     * @throws AbortionException when the aborter kicks in
     */
    public InterestingReferences(final JBCGraph graph, final boolean paperMode, final Abortion aborter)
            throws AbortionException {
        this.heapPositionsCache = new LinkedHashMap<>();
        this.allReferencesCache = new LinkedHashMap<>();

        for (final Node node : graph.getNodes()) {
            for (final Edge edge : node.getOutEdges()) {
                if (paperMode) {
                    this.initalScanEdgePaperMode(edge);
                } else {
                    this.initalScanEdge(edge);
                }
            }
        }

        // run backwards from every single node until nothing was done
        boolean changed;
        do {
            aborter.checkAbortion();
            final Collection<Node> visitedNodes = new LinkedHashSet<>();
            final Collection<Edge> visitedEdges = new LinkedHashSet<>();
            final LinkedList<Pair<Node, Edge>> todo = new LinkedList<>();
            for (final Node node : graph.getNodes()) {
                todo.addFirst(new Pair<Node, Edge>(node, null));
            }
            changed = false;
            while (!todo.isEmpty()) {
                final Pair<Node, Edge> pair = todo.removeFirst();
                final Node node = pair.x;
                final Edge edge = pair.y;

                if (node != null && visitedNodes.add(node)) {
                    final State s = node.getState();
                    if (!paperMode) {
                        changed |= this.propagateInState(s);
                    }

                    for (final Edge inEdge : node.getInEdges()) {
                        final Pair<Node, Edge> newPair =
                            new Pair<>(null, inEdge);
                        todo.addFirst(newPair);
                    }
                }

                if (edge != null && visitedEdges.add(edge)) {
                    if (paperMode) {
                        changed |= this.propagateEdgePaperMode(edge);
                    } else {
                        changed |= this.propagateEdge(edge);
                    }
                    final Pair<Node, Edge> newPair =
                        new Pair<>(edge.getStart(), null);
                    todo.addFirst(newPair);
                }
            }
        } while (changed);
    }

    /**
     * @param ref Some reference
     * @param state Some state in the analyzed SCC
     * @return true iff <code>ref</code> is interesting in <code>node</code>.
     */
    public boolean isOfInterestFor(final AbstractVariableReference ref, final State state) {
        return this.refs.contains(state, ref);
    }

    /**
     * @param state Some state in the analyzed SCC
     * @param ref Some reference
     * @return true iff <code>ref</code> was not already marked as interesting.
     */
    public boolean markAsInteresting(final State state, final AbstractVariableReference ref) {
        return this.markAsInteresting(state, Collections.singleton(ref));
    }

    /**
     * @param state Some state in the analyzed SCC
     * @param references Some references
     * @return true iff any reference in <code>references</code> was not already
     * marked as interesting.
     */
    public boolean markAsInteresting(final State state, final Collection<AbstractVariableReference> references) {
        HeapPositions heap = null;
        if (Globals.DEBUG_MARC) {
            heap = this.getHeapPositions(state);
        }

        boolean added = false;
        for (final AbstractVariableReference ref : references) {
            if (Globals.DEBUG_MARC) {
                if (!(state.getAbstractVariable(ref) instanceof LiteralInt)) {
                    try {
                        final Collection<StatePosition> pos = heap.getPositionsForRef(ref);
                        if (pos == null || pos.size() == 0) {
                            throw new Exception();
                        }
                    } catch (final Throwable e) {
                        //System.out.println("Could not find position for interesting reference ref");
                    }
                }
            }
            if (this.getAllReferences(state).contains(ref)) {
                added |= this.refs.add(state, ref);
            }
        }
        return added;
    }

    /**
     * Initial scan of an edge in the graph, marking those references as
     * interesting that needed information refinement.
     *
     * @param edge some edge in a termination graph
     */
    private void initalScanEdgePaperMode(final Edge edge) {
        final EdgeInformation edgeLabel = edge.getLabel();
        if (edgeLabel instanceof RefinementEdge) {
            final State srcState = edge.getStart().getState();
            final State targetState = edge.getEnd().getState();
            final RefinementEdge refinement = (RefinementEdge) edgeLabel;
            for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> e : refinement.getRefRenaming().entrySet()) {
                this.markAsInteresting(srcState, e.getKey());
                this.markAsInteresting(targetState, e.getValue());
            }
        }
        if (edgeLabel instanceof SplitEdge) {
            final State srcState = edge.getStart().getState();
            final State targetState = edge.getEnd().getState();
            final SplitEdge split = (SplitEdge) edgeLabel;
            final Collection<AbstractVariableReference> allTargetRefs =
                this.getAllReferences(targetState);
            for (final AbstractVariableReference ref : split.getSplitRefs()) {
                this.markAsInteresting(srcState, ref);
                //In the x != y -> false split, one of the vars vanishes:
                if (allTargetRefs.contains(ref)) {
                    this.markAsInteresting(targetState, ref);
                }
            }
        }
    }

    /**
     * Do the initial scan of an edge, noting references that are directly
     * involved in comparisons or typecasts.
     * @param edge some edge from the FIGraph
     */
    private void initalScanEdge(final Edge edge) {
        final Node startNode = edge.getStart();
        final State startState = startNode.getState();
        for (final VariableInformation  info : edge.getLabel()) {
            if (info instanceof ExistenceCheck || info instanceof InstanceCast) {
                this.markAsInteresting(startState, ((ObjectInformation) info).getRef());
            } else if (info instanceof JBCIntegerRelation) {
                final JBCIntegerRelation ir = (JBCIntegerRelation) info;
                if (!ir.leftIntegerIsNoRef()) {
                    this.markAsInteresting(startState, ir.getLeftIntRef());
                }
                if (!ir.rightIntegerIsNoRef()) {
                    this.markAsInteresting(startState, ir.getRightIntRef());
                }
            } else if (info instanceof StaticFieldAccessInformation) {
                final StaticFieldAccessInformation sfa =
                    (StaticFieldAccessInformation) info;
                if (sfa.getAccessType() == FieldAccessRW.WRITE) {
                    this.changedStaticFields.add(new Pair<>(sfa.getClassName(),
                        sfa.getFieldName()));
                }
            }
        }
    }


    /**
     * Propagate information about interesting reference from the edge target
     * to the edge source as described in the nontermination paper:
     *  (1) For Refinement/Instance edges s--s', we ensure that
     *       s|_\pi interesting iff s'|_\pi interesting
     *  (2) For Eval edges s--s' with a label r = r' OP r'' and r interesting
     *      in s', r' and '' are marked as interesting in s.
     *  (3) For eval edges s--s', we ensure that
     *       r interesting in s iff r interesting in s'
     *
     * @param edge some edge from the FIGraph
     * @return true iff new references were marked as interesting
     */
    private boolean propagateEdgePaperMode(final Edge edge) {
        final EdgeInformation edgeLabel = edge.getLabel();
        final State startState = edge.getStart().getState();
        final State endState = edge.getEnd().getState();
        boolean changed = false;

        if (edgeLabel instanceof RefinementOrSplitEdge || edgeLabel instanceof InstanceEdge) {
            final Collection<AbstractVariableReference> endRefs = this.refs.getNotNull(endState);
            final CollectionMap<AbstractVariableReference, AbstractVariableReference> mapEndToStart =
                edge.getRefRenamingEndToStart(this.heapPositionsCache);
            for (final AbstractVariableReference ref : endRefs) {
                if (mapEndToStart.containsKey(ref)) {
                    changed |= this.markAsInteresting(startState, mapEndToStart.get(ref));
                }
            }

            final Collection<AbstractVariableReference> startRefs =
                this.refs.getNotNull(startState);
            final CollectionMap<AbstractVariableReference, AbstractVariableReference> mapStartToEnd =
                edge.getRefRenamingStartToEnd(this.heapPositionsCache);
            for (final AbstractVariableReference ref : startRefs) {
                if (mapStartToEnd.containsKey(ref)) {
                    changed |= this.markAsInteresting(endState, mapStartToEnd.get(ref));
                }
            }
        } else if (edgeLabel instanceof EvaluationEdge || edgeLabel instanceof CallAbstractEdge) {
            final Collection<AbstractVariableReference> allStartRefs =
                this.getAllReferences(startState);
            final Collection<AbstractVariableReference> allEndRefs =
                this.getAllReferences(endState);
            final Collection<AbstractVariableReference> interestingStartRefs =
                this.refs.getNotNull(startState);
            final Collection<AbstractVariableReference> interestingEndRefs =
                this.refs.getNotNull(endState);

            for (final AbstractVariableReference ref : interestingStartRefs) {
                if (allEndRefs.contains(ref)) {
                    changed |= this.markAsInteresting(endState, ref);
                }
            }
            for (final AbstractVariableReference ref : interestingEndRefs) {
                if (allStartRefs.contains(ref)) {
                    changed |= this.markAsInteresting(startState, ref);
                }
            }

            for (final VariableInformation vi : edgeLabel) {
                if (vi instanceof IntegerResultInformation) {
                    final IntegerResultInformation ii =
                        ((IntegerResultInformation) vi);
                    final AbstractVariableReference resRef = ii.getResult();

                    if (this.isOfInterestFor(resRef, endState)) {
                        final AbstractVariableReference opLeftRef =
                            ii.getFirstNumber();
                        if (opLeftRef != null) {
                            changed |= this.markAsInteresting(startState, opLeftRef);
                        }

                        if (!ii.secondIsConstant()) {
                            final AbstractVariableReference opRightRef =
                                ii.getSecondNumber();
                            if (opRightRef != null) {
                                changed |= this.markAsInteresting(startState, opRightRef);
                            }
                        }
                    }
                } else if (vi instanceof AbstractInstanceAccessInformation
                    || vi instanceof AbstractArrayAccessInformation) {
                    final ReferenceAccessInformation rai =
                        (ReferenceAccessInformation) vi;
                    if (rai.getAccessType() == FieldAccessRW.READ) {
                        final AbstractVariableReference readRef = rai.getReadOrWrittenRef();
                        if (interestingEndRefs.contains(readRef)) {
                            this.markAsInteresting(startState, rai.getAccessedRef());
                        }
                    }
                } else if (vi instanceof ArrayLengthInfo) {
                    final ArrayLengthInfo ali = (ArrayLengthInfo) vi;
                    final AbstractVariableReference readRef = ali.getLengthReference();
                    if (interestingEndRefs.contains(readRef)) {
                        this.markAsInteresting(startState, ali.getArrayReference());
                    }
                }
            }
        }

        return changed;
    }

    /**
     * Propagate information about interesting reference from the edge target
     * to the edge source. References in the source which are used to construct
     * an interesting reference in the target (by field access, arithmetic
     * computation, ...) then become interesting in the source.
     *
     * @param edge some edge from the FIGraph
     * @return true iff new references were marked as interesting
     */
    private boolean propagateEdge(final Edge edge) {
        final EdgeInformation edgeInfo = edge.getLabel();
        final Node startNode = edge.getStart();
        final State startState = startNode.getState();
        final Node endNode = edge.getEnd();
        final State endState = endNode.getState();

        boolean newRef = false;

        for (final VariableInformation info : edge.getLabel()) {
            if (info instanceof ReferenceAccessInformation) {
                final ReferenceAccessInformation ra = (ReferenceAccessInformation) info;
                /*
                 * If the ref read from is of interest, we want to know its
                 * value, so encode the enclosing reference in the start state:
                 */
                if (ra.isRead() && this.refs.contains(endState, ra.getReadOrWrittenRef())) {
                    newRef |= this.markAsInteresting(startState, ra.getAccessedRef());
                /*
                 * If the ref written to is of interest, we want to know what's
                 * in there, so encode the written reference in the start state:
                 */
                } else if (ra.isWrite() && this.refs.contains(endState, ra.getAccessedRef())) {
                    newRef |= this.markAsInteresting(startState, ra.getReadOrWrittenRef());
                }
            }

            //If the array length will be of interest, mark the array as interesting:
            if (info instanceof ArrayLengthInfo) {
                final ArrayLengthInfo ali = (ArrayLengthInfo) info;
                if (this.refs.contains(endState, ali.getLengthReference())) {
                    newRef |= this.markAsInteresting(startState, ali.getArrayReference());
                }
            }

            //If a result is interesting, mark the operands as interesting:
            if (info instanceof IntegerResultInformation) {
                final IntegerResultInformation iri = (IntegerResultInformation) info;
                if (this.refs.contains(endState, iri.getResult())) {
                    if (!iri.secondIsConstant()) {
                        newRef |=
                            this.markAsInteresting(startState, iri.getSecondNumber());
                    }
                    if (iri.getFirstNumber() != null) {
                        newRef |= this.markAsInteresting(startState, iri.getFirstNumber());
                    }
                }
            }
        }

        //For evaluations, just copy all interesting references from target to source:
        if (edgeInfo instanceof EvaluationEdge
            || edgeInfo instanceof CallAbstractEdge
            || edgeInfo instanceof InitializationStateChange) {
            newRef |= this.markAsInteresting(startState, this.refs.getNotNull(endState));
            newRef |= this.markAsInteresting(endState, this.refs.getNotNull(startState));

        /* For refinements and instantiations, map references in source and   *
         * target onto each other, then use this map to propagate the         *
         * interesting information:                                           */
        } else {
            final Collection<AbstractVariableReference> endRefs =
                this.refs.getNotNull(endState);
            final CollectionMap<AbstractVariableReference, AbstractVariableReference> mapEndToStart =
                edge.getRefRenamingEndToStart(this.heapPositionsCache);
            for (final AbstractVariableReference ref : endRefs) {
                if (ref != null && ref.isNULLRef()) {
                    newRef |= this.markAsInteresting(startState, ref);
                } else if (mapEndToStart.containsKey(ref)) {
                    newRef |= this.markAsInteresting(startState, mapEndToStart.get(ref));
                }
            }

            final Collection<AbstractVariableReference> startRefs =
                this.refs.getNotNull(startState);
            final CollectionMap<AbstractVariableReference, AbstractVariableReference> mapStartToEnd =
                edge.getRefRenamingStartToEnd(this.heapPositionsCache);
            for (final AbstractVariableReference ref : startRefs) {
                if (ref != null && ref.isNULLRef()) {
                    newRef |= this.markAsInteresting(endState, ref);
                } else if (mapStartToEnd.containsKey(ref)) {
                    newRef |= this.markAsInteresting(endState, mapStartToEnd.get(ref));
                }
            }
        }

        return newRef;
    }

    /**
     * Propagate interesting references in a state. Ensures that each
     * interesting reference can be reached by a path of interesting references.
     * (Is a horrible over-approximation right now)
     *
     * @param s some state
     * @return true if new references were marked as interesting
     */
    private boolean propagateInState(final State s) {
        final Collection<AbstractVariableReference> interestingRefs =
            this.refs.getNotNull(s);
        final Collection<AbstractVariableReference> checked =
            this.checkedToRoot.getNotNullAndAdd(s);
        final HeapPositions heapPos = this.getHeapPositions(s);
        final CollectionMap<AbstractVariableReference, StatePosition> referencesAndPos =
            heapPos.getReferencesAndPositions();
        final Set<AbstractVariableReference> newInterestingRefs =
            new LinkedHashSet<>();

        for (final Entry<AbstractVariableReference, Collection<StatePosition>> e : referencesAndPos.entrySet()) {
            final AbstractVariableReference ref = e.getKey();

            //Ignore constants.
            if (ref.pointsToConstant()) {
                continue;
            }

            if (!checked.add(ref)) {
                continue;
            }

            final Collection<StatePosition> positions = e.getValue();

            final AbstractVariable val = s.getAbstractVariable(ref);
            if (val instanceof Array) {
                for (final AbstractVariableReference childRef : ((Array) val).getReferences().keySet()) {
                    if (interestingRefs.contains(childRef)) {
                        newInterestingRefs.add(ref);
                        break;
                    }
                }
            } else if (val instanceof ConcreteInstance) {
                for (final AbstractVariableReference childRef : ((ConcreteInstance) val).getReferences()) {
                    if (interestingRefs.contains(childRef)) {
                        newInterestingRefs.add(ref);
                        break;
                    }
                }
            }

            if (!ref.isNULLRef() && interestingRefs.contains(ref) || newInterestingRefs.contains(ref)) {
                for (final StatePosition pos : positions) {
                    //This pushes in all references reaching pos:
                    pos.getReferencesOnPath(s, newInterestingRefs);
                }
            }
        }

        return this.markAsInteresting(s, newInterestingRefs);
    }

    /**
     * Make use of a cache.
     * @param s a state
     * @return the heap positions for the given state
     */
    private HeapPositions getHeapPositions(final State s) {
        HeapPositions result = this.heapPositionsCache.get(s);
        if (result == null) {
            result = new HeapPositions(s, true);
            this.heapPositionsCache.put(s, result);
        }
        return result;
    }

    /**
     * Make use of a cache.
     * @param s a state
     * @return all references in the given state
     */
    private Collection<AbstractVariableReference> getAllReferences(final State s) {
        Collection<AbstractVariableReference> allRefs =
            this.allReferencesCache.get(s);
        if (allRefs == null) {
            if (this.heapPositionsCache.containsKey(s)) {
                final HeapPositions heapPos = this.heapPositionsCache.get(s);
                allRefs = heapPos.getReferencesAndPositions().keySet();
            } else {
                allRefs = s.getReferences().keySet();
            }
            this.allReferencesCache.put(s, allRefs);
        }
        return allRefs;
    }

    /**
     * Update the interesting references sets for new nodes, without
     * propagating any information completely through the graph.
     *
     * @param n some node not known when constructing the initial object
     * @param es edges connecting the new node to the already known nodes.
     */
    public void addNode(final Node n, final Collection<Edge> es) {
        for (final Edge e : es) {
            this.propagateEdge(e);
        }
    }

    /**
     * @param cName some classname
     * @param fieldName some string describing a field in <code>cName</code>
     * @return true if the described field is not changed in the considered
     *  graph.
     */
    public boolean isUnchangedStaticField(final ClassName cName, final String fieldName) {
        return !this.changedStaticFields.contains(new Pair<>(cName, fieldName));
    }

    /**
     * @param s some state
     * @return a copy of the stored set of interesting references for this state.
     */
    public Set<AbstractVariableReference> getInterestingRefs(final State s) {
        return new LinkedHashSet<>(this.refs.getNotNull(s));
    }

    /**
     * @param s some state
     * @return the set of interesting positions in this state.
     */
    public Set<StatePosition> getInterestingPositions(final State s) {
        final LinkedHashSet<StatePosition> result = new LinkedHashSet<>();
        final HeapPositions heapPos = this.getHeapPositions(s);
        for (final AbstractVariableReference ref : this.refs.getNotNull(s)) {
            StatePosition shortestPos = heapPos.getShortestPositionForRef(ref);

            // witness states do not have input references, so avoid picking these positions
            if (shortestPos.getRootPosition() instanceof RootIRPosition) {
                for (final StatePosition pos : heapPos.getPositionsForRef(ref)) {
                    if (pos.getRootPosition() instanceof RootIRPosition) {
                        continue;
                    }
                    if (pos.length() == shortestPos.length()) {
                        shortestPos = pos;
                        break;
                    }
                }
            }
            result.add(shortestPos);
        }
        return result;
    }
}
