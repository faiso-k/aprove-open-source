package aprove.verification.oldframework.Bytecode.Merger;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * The path merger is designed to closely follow the definitions based on
 * "state positions" (e.g. in Marc's thesis and the papers). To work with
 * positions and references that can be reached using multiple paths, the class
 * HeapPositions is used.
 * @author cotto
 */
public class PathMerger extends JBCMerger.JBCMergerSkeleton {

    /**
     * Provide an instance of this merger so that 'isInstance(A, B)' can be
     * used.
     * @see JBCMerger#isInstance(State, State)
     */
    public PathMerger() {
        super();
    }

    /**
     * Merge A with given states B such that A and B are instances of the
     * resulting state C. Here, the abstraction needed to generate C is
     * minimized.
     * @see JBCMerger#merge(State)
     * @param a A
     */
    public PathMerger(final State a) {
        super(a);
    }

    /**
     * Find a state C for the given state A and the B candidates, such that A
     * and B are instances of C. Here, the abstraction needed to generate C is
     * minimized. Furthermore, only results with cost not exceeding the given
     * maximum are returned.
     * @see JBCMerger#isInstance(State, State) to only find out if one state is an
     * instance of the other state.
     * @param a A
     * @param maximalCosts If null, enforces a merge. If <= 0, only finds states
     * of which <code>A</code> is an instance of. If > 0, finds states where the
     * needed abstraction is limited.
     */
    public PathMerger(final State a, final Double maximalCosts) {
        // limit cost
        super(a, maximalCosts);
    }

    /**
     * -><-, Def. 2h and 2i. If s'|pi -><- s'|pi' then s|piBAR -><- s|pi'BAR
     * @param newResult Merge result to be constructed
     * @param fromLeft Indicate if our state is left merge partner
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void addMergedJoins(final JBCMergeResult newResult, final boolean fromLeft)
        throws TooExpensiveException
    {
        final HeapPositions heapPos = newResult.getHeapPositions(fromLeft);
        final HeapPositions mergedHeapPos = newResult.getHeapPositionsC();

        final State thisState = heapPos.getState();
        final JoiningStructures joins = thisState.getHeapAnnotations().getJoiningStructures();

        for (final TwoRefs t : joins.getJoinsAnnotations()) {
            final AbstractVariableReference leftRef = t.getRefOne();
            final AbstractVariableReference rightRef = t.getRefTwo();
            for (final StatePosition leftPos : heapPos.getPositionsForRef(leftRef)) {
                for (final StatePosition rightPos : heapPos.getPositionsForRef(rightRef)) {
                    // We have s|leftPos -><- s|rightPos in this/thatState
                    for (final PrefixResult mergedLeft : mergedHeapPos.getMaxRealizedPrefixes(leftPos, heapPos)) {
                        final AbstractVariableReference mergedLeftRef = mergedLeft.getReference();
                        for (final PrefixResult mergedRight : mergedHeapPos.getMaxRealizedPrefixes(rightPos, heapPos)) {
                            final AbstractVariableReference mergedRightRef = mergedRight.getReference();

                            PathMerger.addJoins(
                                leftRef,
                                rightRef,
                                mergedLeftRef,
                                mergedRightRef,
                                mergedLeft.getPosition(),
                                mergedRight.getPosition(),
                                newResult,
                                fromLeft);
                        }
                    }
                }
            }
        }
    }

    /**
     * Add a joins annotation for the two given references, if it does not exist
     * yet. Also add appropriate costs.
     * @param thisLeftRef the left ref of the joins/equality in the source state
     * @param thisRightRef the right ref of the joins/equality in the source state
     * @param refOne the left reference of the new joins annotation
     * @param refTwo the right reference of the new joins annotation
     * @param posOne the position leading to the left reference
     * @param posTwo the position leading to the right reference
     * @param newResult the result being constructed
     * @param fromLeft Indicate if our state is left merge partner
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void addJoins(
        final AbstractVariableReference thisLeftRef,
        final AbstractVariableReference thisRightRef,
        final AbstractVariableReference refOne,
        final AbstractVariableReference refTwo,
        final StatePosition posOne,
        final StatePosition posTwo,
        final JBCMergeResult newResult,
        final boolean fromLeft) throws TooExpensiveException
    {

        final JoiningStructures joinsOther =
            newResult.getHeapPositions(!fromLeft).getState().getHeapAnnotations().getJoiningStructures();

        final State mergedState = newResult.getMergedState();
        final HeapAnnotations mergedAnnotations = mergedState.getHeapAnnotations();
        final JoiningStructures joinsMerged = mergedAnnotations.getJoiningStructures();

        //Do not add self-joins for tree-shaped references:
        if (refOne.equals(refTwo)
            && !mergedAnnotations.getCyclicStructures().isCyclic(refOne)
            && !mergedAnnotations.getPossiblyNonTreeRefs().contains(refOne))
        {
            return;
        }
        //Do not add joins only usable in non-tree forms when the non-tree annotation is missing:
        if (!mergedAnnotations.isPossiblyNonTree(refOne)
            && Reachability.getReachableRefs(refTwo, false, mergedState).contains(refOne))
        {
            return;
        }
        if (mergedState.isFullyRealized(refOne) && mergedState.isFullyRealized(refTwo)) {
            // both references already are realized, there is no need for a joins annotation
            return;
        }
        if (joinsMerged.add(refOne, refTwo)) {
            final HeapPositions heapPositionsOther = newResult.getHeapPositions(!fromLeft);
            final AbstractVariableReference otherRefOne = heapPositionsOther.getReferenceForPos(posOne, true);
            final AbstractVariableReference otherRefTwo = heapPositionsOther.getReferenceForPos(posTwo, true);
            if (otherRefOne == null || otherRefTwo == null || !joinsOther.areJoining(otherRefOne, otherRefTwo)) {
                final Collection<AbstractVariableReference> theseRefs = new LinkedList<>();
                theseRefs.add(thisLeftRef);
                theseRefs.add(thisRightRef);
                final Collection<AbstractVariableReference> thoseRefs = new LinkedList<>();
                thoseRefs.add(otherRefOne);
                thoseRefs.add(otherRefTwo);
                newResult.addCost(CostType.POSSIBLY_JOINING, theseRefs, thoseRefs, 1, fromLeft);
            }
        }
    }

    /**
     * Introduce annotations for realized non-tree or cyclic shapes in the state
     * defined by isThisState that are not represented in the merged state.
     * @param newResult the result being constructed
     * @param isThisState true if the state for refsWithMultiplePositions is
     * thatState
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void addNonTreeAndCyclic(final JBCMergeResult newResult, final boolean isThisState)
        throws TooExpensiveException
    {
        final HeapPositions heapPositions = newResult.getHeapPositions(isThisState);
        final CollectionMap<AbstractVariableReference, StatePosition> refsWithMultiplePositions =
            heapPositions.getRefsWithMultiplePositions();
        final HeapPositions heapPositionsMerged = newResult.getHeapPositionsC();
        for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> e : refsWithMultiplePositions
            .entrySet())
        {
            for (final Pair<StatePosition, StatePosition> pair : Collection_Util.getPairs(e.getValue())) {
                final StatePosition posOne = pair.x;
                final StatePosition posTwo = pair.y;

                final StatePosition nonTreeStartPos = posOne.getMaxCommonPrefix(posTwo);

                if (nonTreeStartPos == null) {
                    /*
                     * No common prefix, just two paths leading to the
                     * same reference. This is handled when introducing
                     * possible equality/joins (Def. 2g)
                     */
                    continue;
                }

                StatePosition longerPosition;
                Collection<HeapEdge> neededEdges;
                if (nonTreeStartPos.equals(posOne)) {
                    longerPosition = posTwo;
                    neededEdges = posTwo.getEdgesTo(nonTreeStartPos);
                } else if (nonTreeStartPos.equals(posTwo)) {
                    longerPosition = posOne;
                    neededEdges = posOne.getEdgesTo(nonTreeStartPos);
                } else {
                    longerPosition = null;
                    neededEdges = null;
                }

                /*
                 * maxPrefix != null means we have a non-tree shape in the state
                 * described by isThisState (which is not given as an argument).
                 * Now we need to find out if this shape is also represented in
                 * the merged state.
                 */
                for (final PrefixResult prefixOne : heapPositionsMerged.getMaxRealizedPrefixes(posOne, heapPositions)) {
                    for (final PrefixResult prefixTwo : heapPositionsMerged.getMaxRealizedPrefixes(
                        posTwo,
                        heapPositions))
                    {
                        final AbstractVariableReference refOne = prefixOne.getReference();
                        final AbstractVariableReference refTwo = prefixTwo.getReference();
                        if (prefixOne.isRealized() && prefixTwo.isRealized() && refOne.equals(refTwo)) {
                            /*
                             * In the merged state this non-tree/cycle is
                             * realized, so nothing needs to be done here.
                             */
                            continue;
                        }

                        /*
                         * The non-tree shape is not realized in the merged
                         * state. Now we need to add at least a non-tree
                         * annotation to the references which are prefixes of
                         * nonTreeStartPos.
                         */

                        PathMerger.setNonTree(newResult, nonTreeStartPos, isThisState);
                        if (longerPosition != null) {
                            // there is a cycle
                            // for all references on the cycle, add non-tree and cyclic annotation
                            for (final StatePosition pos : longerPosition.getPositionsDownTo(nonTreeStartPos)) {
                                PathMerger.setNonTree(newResult, pos, isThisState);
                                PathMerger.setCyclic(newResult, pos, neededEdges, isThisState);
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Collect the positions where x = y or x =?= y holds in the given state, so
     * that the annotations demanded by Def. 2g can be added.
     * @param isThisState true iff this is the "left" state.
     * @param newResult the new merge result
     * @param todo the positions are added here
     */
    private static void collectMoreNeededEqualityAnnotations(
        final boolean isThisState,
        final JBCMergeResult newResult,
        final Collection<Triple<StatePosition, StatePosition, HeapPositions>> todo)
    {
        final HeapPositions heapPositions = newResult.getHeapPositions(isThisState);
        final CollectionMap<AbstractVariableReference, StatePosition> refsWithMultiplePositions =
            heapPositions.getRefsWithMultiplePositions();
        final State state = heapPositions.getState();
        final EqualityGraph eGraph = state.getHeapAnnotations().getEqualityGraph();
        JBCOptions options = state.getJBCOptions();

        /*
         * First handle the existing annotations.
         */
        for (final AbstractVariableReference refOne : eGraph.getReferences()) {
            for (final AbstractVariableReference refTwo : eGraph.getPartners(refOne)) {
                /*
                 * If both references are possibly Strings (or both are possible
                 * Class instances), we do not need to add joins annotations,
                 * because the equality we need to express here is regarded
                 * implicitly.
                 */
                    final AbstractType atOne = state.getAbstractType(refOne);
                    final AbstractType atTwo = state.getAbstractType(refTwo);
                    if (options.simplifiedStringHandling() && atOne.containsStringType() && atTwo.containsStringType()) {
                        continue;
                    }
                    if (options.simplifiedClassHandling() && atOne.containsClassType() && atTwo.containsClassType()) {
                        continue;
                    }

                // we have refOne =?= refTwo in state
                for (final StatePosition posOne : heapPositions.getPositionsForRef(refOne)) {
                    for (final StatePosition posTwo : heapPositions.getPositionsForRef(refTwo)) {
                        /*
                         * We have s'|posOne =?= s'|posTwo, so we need to
                         * introduce at least one joins annotation if any of the
                         * represented positions is not realized in the merged
                         * state.
                         */
                        final Triple<StatePosition, StatePosition, HeapPositions> triple =
                            new Triple<>(posOne, posTwo, heapPositions);
                        todo.add(triple);
                    }
                }
            }
        }

        // handle s'|pos = s'|pos'
        for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> e : refsWithMultiplePositions
            .entrySet())
        {
            final Collection<StatePosition> positions = e.getValue();
            /*
             * OK, now we have at least two positions reaching the same
             * reference. This means s'|pos = s'|pos' for all pairs pos, pos'
             * in this collection.
             */

            // add all (sorted) pairs of two
            for (final Pair<StatePosition, StatePosition> pair : Collection_Util.getPairs(positions)) {
                final Triple<StatePosition, StatePosition, HeapPositions> triple =
                    new Triple<>(pair.x, pair.y, heapPositions);
                todo.add(triple);
            }
        }
    }

    /**
     * @return a fresh {@link AbstractVariableReference}, indicating the right
     * type
     * @param thisVarRef some {@link AbstractVariableReference}
     * @param thatVarRef some other {@link AbstractVariableReference}
     */
    private static AbstractVariableReference getNewNonPrimitiveVarRef(
        final AbstractVariableReference thisVarRef,
        final AbstractVariableReference thatVarRef)
    {
        if ((thisVarRef.pointsToArray() || thatVarRef.pointsToArray())
            && (thisVarRef.pointsToArray() || thisVarRef.isNULLRef())
            && (thatVarRef.pointsToArray() || thatVarRef.isNULLRef()))
        {
            // at least one is an array, and the other may only be the null pointer
            return new AbstractVariableReference(UIDGenerator.getArrayUIDGenerator().next(), OperandType.ARRAY);
        }
        /*
         * Both are regular object instances or some array is merged with some
         * object (which must be of type jLO).
         */
        return new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);
    }

    /**
     * Handle the implications from Def. 2g, e.g. introducing joins for
     * (possibly) equal references where at least one of the positions is not
     * represented in the merged state.
     * @param todo the collected positions pos1, pos2 with s'|pos1 = s'|pos2 or
     * s'|pos1 =?= s'|pos2 (the same for s). Additionally the HeapPositions
     * object of the corresponding state is given.
     * @param newResult the new merge result
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void handleTodo(
        final Collection<Triple<StatePosition, StatePosition, HeapPositions>> todo,
        final JBCMergeResult newResult) throws TooExpensiveException
    {
        final State mergedState = newResult.getMergedState();
        final HeapPositions mergedHeapPositions = newResult.getHeapPositionsC();
        final EqualityGraph mergedEqualityGraph = mergedState.getHeapAnnotations().getEqualityGraph();

        for (final Triple<StatePosition, StatePosition, HeapPositions> triple : todo) {
            /*
             * The two positions are returned by
             *  - getPositionsForRef (s|posOne =?= s|posTwo)
             *    and
             *  - getRefsWithMultiplePositions (s|posOne = s|posTwo)
             */
            final HeapPositions originalHeapPos = triple.z;
            final StatePosition posOne = triple.x;
            final AbstractVariableReference refOne = originalHeapPos.getReferenceForPos(posOne, true);
            final StatePosition posTwo = triple.y;
            final AbstractVariableReference refTwo = originalHeapPos.getReferenceForPos(posTwo, true);

            final boolean isThis = originalHeapPos.getState() == newResult.getHeapPositionsA().getState();
            for (final PrefixResult prefixOneMerged : mergedHeapPositions.getMaxRealizedPrefixes(
                posOne,
                originalHeapPos))
            {
                final AbstractVariableReference refOneMerged = prefixOneMerged.getReference();
                for (final PrefixResult prefixTwoMerged : mergedHeapPositions.getMaxRealizedPrefixes(
                    posTwo,
                    originalHeapPos))
                {
                    final AbstractVariableReference refTwoMerged = prefixTwoMerged.getReference();
                    if (prefixOneMerged.isRealized() && prefixTwoMerged.isRealized()) {
                        /*
                         * We have both posOne and posTwo in StatePos(s), so we
                         * already handled this in mergeEqualityGraphs (2f) by
                         * construction (2e).
                         */
                        assert (refOneMerged.equals(refTwoMerged) || mergedEqualityGraph.areMarkedAsPossiblyEqual(
                            refOneMerged,
                            refTwoMerged));
                    } else if (prefixOneMerged.isRealized()) {
                        PathMerger.addJoins(
                            refOne,
                            refTwo,
                            refTwoMerged,
                            refOneMerged,
                            prefixTwoMerged.getPosition(),
                            prefixOneMerged.getPosition(),
                            newResult,
                            isThis);
                    } else if (prefixTwoMerged.isRealized()) {
                        PathMerger.addJoins(
                            refOne,
                            refTwo,
                            refOneMerged,
                            refTwoMerged,
                            prefixOneMerged.getPosition(),
                            prefixTwoMerged.getPosition(),
                            newResult,
                            isThis);
                    } else {
                        // both positions are not realized
                        if (refOneMerged.equals(refTwoMerged) && prefixOneMerged.sameSuffix(prefixTwoMerged)) {
                            /*
                             * If these are equal, we reach the same reference
                             * and the remainder of both paths is the same, so
                             * we know that we will reach the same reference for
                             * every instance of this abstract state.
                             */
                            continue;
                        }
                        PathMerger.addJoins(
                            refOne,
                            refTwo,
                            refTwoMerged,
                            refOneMerged,
                            prefixTwoMerged.getPosition(),
                            prefixOneMerged.getPosition(),
                            newResult,
                            isThis);
                        PathMerger.addJoins(
                            refOne,
                            refTwo,
                            refOneMerged,
                            refTwoMerged,
                            prefixOneMerged.getPosition(),
                            prefixTwoMerged.getPosition(),
                            newResult,
                            isThis);
                    }
                }
            }
        }
    }

    /**
     * Take care that the merged state contains a superset of the annotations
     * of the original states.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeAnnotations(final State thisState, final State thatState, final JBCMergeResult newResult)
        throws TooExpensiveException
    {
        final State mergedState = newResult.getMergedState();
        // first, copy all the existing =?= annotations

        // =?=, Def. 2f
        final EqualityGraph thisEqG = thisState.getHeapAnnotations().getEqualityGraph();
        final EqualityGraph thatEqG = thatState.getHeapAnnotations().getEqualityGraph();
        final EqualityGraph mergedEqG = mergedState.getHeapAnnotations().getEqualityGraph();

        JBCMergerSkeleton.mergeEqualityGraphs(thisEqG, thatEqG, mergedEqG, newResult, true);
        JBCMergerSkeleton.mergeEqualityGraphs(thatEqG, thisEqG, mergedEqG, newResult, false);

        /*
         * Calculate new equalities for positions that exist in the merged
         * state. Important: First run mergeEqualityGraphs!
         */
        JBCMergerSkeleton.addNewEqualityAnnotations(thisState, thatState, newResult);

        newResult.createHeapPositions(thisState, thatState, mergedState);

        //Now that we have final heap positions, extend the reachable type information, then merge it:
        PathMerger.mergeReachableTypeInformation(newResult);

        // non-tree, Def. 2j
        PathMerger.mergeNonTreeAnnotations(newResult, true);
        PathMerger.mergeNonTreeAnnotations(newResult, false);

        // cyclic, Def. 2k
        PathMerger.mergeCyclicAnnotations(newResult, true);
        PathMerger.mergeCyclicAnnotations(newResult, false);

        // realized DAGs/cycles, Def. 2l and 2m
        PathMerger.addNonTreeAndCyclic(newResult, true);
        PathMerger.addNonTreeAndCyclic(newResult, false);

        /*
         * We need to do this at the end, so that know when not to add
         * unneeded joins annotations.
         */

        // 2g
        final Collection<Triple<StatePosition, StatePosition, HeapPositions>> todo = new LinkedHashSet<>();
        PathMerger.collectMoreNeededEqualityAnnotations(true, newResult, todo);
        PathMerger.collectMoreNeededEqualityAnnotations(false, newResult, todo);
        PathMerger.handleTodo(todo, newResult);

        /*
         * -><-, Def. 2h and 2i
         * If s'|pi -> s'|pi' then s|piBAR -> s|pi'BAR
         */
        PathMerger.addMergedJoins(newResult, true);
        PathMerger.addMergedJoins(newResult, false);

        PathMerger.addDefinitiveReachabilities(newResult);

        PathMerger.addArrayInfo(newResult, true);
        PathMerger.addArrayInfo(newResult, false);
    }

    /**
     * Have a look at the indicated state. For each array info add it to the merge result, if we know that the
     * information also is contained in the other state. For every lost information, add costs.
     * @param newResult the result being constructed
     * @param isThisState true if the state we look at is thisState
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void addArrayInfo(final JBCMergeResult newResult, final boolean isThisState)
        throws TooExpensiveException
    {
        final State state = newResult.getHeapPositions(isThisState).getState();
        final State otherState = newResult.getHeapPositions(!isThisState).getState();
        for (final Triple<AbstractVariableReference, AbstractVariableReference, AbstractVariableReference> triple : state
            .getHeapAnnotations()
            .getArrayInfo()
            .getTriples())
        {
            final AbstractVariableReference arrayRef = triple.x;
            final AbstractVariableReference indexRef = triple.y;
            final AbstractVariableReference contentRef = triple.z;
            for (final AbstractVariableReference arrayPartner : newResult.getVarCache().getPartners(
                arrayRef,
                isThisState))
            {
                for (final AbstractVariableReference indexPartner : newResult.getVarCache().getPartners(
                    indexRef,
                    isThisState))
                {
                    for (final AbstractVariableReference contentPartner : newResult.getVarCache().getPartners(
                        contentRef,
                        isThisState))
                    {
                        if (PathMerger.checkArrayInfo(arrayPartner, indexPartner, contentPartner, otherState)) {
                            // we found the information, add it to the merged state
                            final AbstractVariableReference arrayRefMerged =
                                newResult.getVarCache().get(arrayRef, arrayPartner, isThisState);
                            final AbstractVariableReference indexRefMerged =
                                newResult.getVarCache().get(indexRef, indexPartner, isThisState);
                            final AbstractVariableReference contentRefMerged =
                                newResult.getVarCache().get(contentRef, contentPartner, isThisState);
                            newResult
                                .getMergedState()
                                .getHeapAnnotations()
                                .getArrayInfo()
                                .add(arrayRefMerged, indexRefMerged, contentRefMerged);
                        } else {
                            // the information is not represented in the other state, add costs
                            final Collection<AbstractVariableReference> leftRefs = new LinkedHashSet<>();
                            leftRefs.add(triple.x);
                            leftRefs.add(triple.y);
                            leftRefs.add(triple.z);
                            final Collection<AbstractVariableReference> rightRefs = new LinkedHashSet<>();
                            rightRefs.add(arrayPartner);
                            rightRefs.add(indexPartner);
                            rightRefs.add(contentPartner);
                            newResult.addCost(CostType.LOST_ARRAYINFO, leftRefs, rightRefs, 1.0, !isThisState);
                        }
                    }
                }
            }
        }
    }

    /**
     * @param arrayRef a reference
     * @param indexRef a reference
     * @param contentRef a reference
     * @param state a state
     * @return true only if array[index] = content holds in the given state
     */
    private static boolean checkArrayInfo(
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef,
        final AbstractVariableReference contentRef,
        final State state)
    {
        // annotation?
        if (contentRef.equals(state.getHeapAnnotations().getArrayInfo().get(arrayRef, indexRef))) {
            return true;
        }

        // concrete array?
        final AbstractVariable var = state.getAbstractVariable(arrayRef);
        if (var instanceof ConcreteArray && indexRef.pointsToConstantInt()) {
            final AbstractInt aInt = (AbstractInt) state.getAbstractVariable(indexRef);
            final int index = aInt.getLiteral().intValue();
            final ConcreteArray array = (ConcreteArray) var;
            final AbstractVariableReference content = array.getData()[index];
            if (contentRef.equals(content)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Add reachable type information to cover abstracted successors.
     *
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeReachableTypeInformation(final JBCMergeResult newResult) throws TooExpensiveException {
        JBCOptions options = newResult.getHeapPositionsA().getState().getJBCOptions();
        final HeapPositions mergedHeapPos = newResult.getHeapPositionsC();
        final Map<StatePosition, Collection<AbstractType>> reachableTypesLeft =
            PathMerger.computeReachableTypes(newResult.getHeapPositionsA(), mergedHeapPos);
        final Map<StatePosition, Collection<AbstractType>> reachableTypesRight =
            PathMerger.computeReachableTypes(newResult.getHeapPositionsB(), mergedHeapPos);

        //Because of null refs, we need the union of the sets:
        final Set<StatePosition> reachableRefPositions = new LinkedHashSet<>();
        reachableRefPositions.addAll(reachableTypesLeft.keySet());
        reachableRefPositions.addAll(reachableTypesRight.keySet());

        final State mergedState = newResult.getMergedState();
        final ClassPath cPath = mergedState.getClassPath();

        final AbstractType[] dummyATArray = new AbstractType[0];
        for (final StatePosition pos : reachableRefPositions) {

            final AbstractType leftReachableTypes;
            final AbstractVariableReference leftRef;
            if (reachableTypesLeft.containsKey(pos)) {
                leftReachableTypes = AbstractType.union(cPath, options, reachableTypesLeft.get(pos).toArray(dummyATArray));
                leftRef = newResult.getHeapPositionsA().getReferenceForPos(pos, true);
            } else {
                leftReachableTypes = new AbstractType(cPath, FuzzyClassType.FT_JAVA_LANG_OBJECT);
                leftRef = null;
            }

            final AbstractType rightReachableTypes;
            final AbstractVariableReference rightRef;
            if (reachableTypesRight.containsKey(pos)) {
                rightReachableTypes = AbstractType.union(cPath, options, reachableTypesRight.get(pos).toArray(dummyATArray));
                rightRef = newResult.getHeapPositionsB().getReferenceForPos(pos, true);
            } else {
                rightReachableTypes = new AbstractType(cPath, FuzzyClassType.FT_JAVA_LANG_OBJECT);
                rightRef = null;
            }

            final AbstractType newReachableTypes = AbstractType.union(cPath, options, leftReachableTypes, rightReachableTypes);

            if (!leftReachableTypes.containsAll(newReachableTypes, cPath, options)) {
                newResult.addCost(CostType.LOST_TYPEINFO, leftRef, rightRef, false);
            }
            if (!rightReachableTypes.containsAll(newReachableTypes, cPath, options)) {
                newResult.addCost(CostType.LOST_TYPEINFO, rightRef, leftRef, true);
            }

            mergedState
                .getHeapAnnotations()
                .setReachableTypes(mergedHeapPos.getReferenceForPos(pos), newReachableTypes);

        }
    }

    /**
     * @param oldHeapPos the heap positions of one of the merged states
     * @param mergedHeapPos the heap positions of the merge result
     * @return a mapping of each state position in mergedHeapPos to a
     *  collection of types describing all possibly following, abstracted
     *  reachable types in the state of oldHeapPos.
     */
    private static CollectionMap<StatePosition, AbstractType> computeReachableTypes(
        final HeapPositions oldHeapPos,
        final HeapPositions mergedHeapPos)
    {
        final HeapAnnotations oldStateAnnotations = oldHeapPos.getState().getHeapAnnotations();
        final CollectionMap<StatePosition, AbstractType> res = new CollectionMap<>();
        for (final Entry<AbstractVariableReference, Collection<StatePosition>> e : oldHeapPos
            .getReferencesAndPositions()
            .entrySet())
        {
            final AbstractVariableReference ref = e.getKey();
            if (ref.isNULLRef()) {
                continue;
            }
            final AbstractType oldReachableTypes = oldStateAnnotations.getReachableTypes(ref);
            final AbstractType refType = oldStateAnnotations.getAbstractType(ref);
            for (final StatePosition oldPos : e.getValue()) {
                final Collection<PrefixResult> prefixes = mergedHeapPos.getMaxRealizedPrefixes(oldPos, oldHeapPos);
                for (final PrefixResult prefix : prefixes) {
                    if (oldReachableTypes != null) {
                        res.add(prefix.getPosition(), oldReachableTypes);
                    }
                    //If we abstracted:
                    if (!prefix.isRealized()) {
                        res.add(prefix.getPosition(), refType);
                    }
                }
            }
        }
        return res;
    }

    /**
     * Add as many DefiniteReachability annotations to the merged state as possible.
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void addDefinitiveReachabilities(final JBCMergeResult newResult) throws TooExpensiveException {
        final HeapPositions originHeapPositionsA = newResult.getHeapPositionsA();
        final HeapPositions originHeapPositionsB = newResult.getHeapPositionsB();
        final HeapPositions heapPosTarget = newResult.getHeapPositionsC();

        final Set<DefiniteReachabilityAnnotation> annotationsForThisState =
            DefiniteReachabilityAnnotation.getCommonConnections(originHeapPositionsA, heapPosTarget);
        final Set<DefiniteReachabilityAnnotation> annotationsForThatState =
            DefiniteReachabilityAnnotation.getCommonConnections(originHeapPositionsB, heapPosTarget);

        // throw out annotations x -{f}!-> y where y is maybe existing

        final State mergedState = newResult.getMergedState();
        final HeapAnnotations ha = mergedState.getHeapAnnotations();
        final Collection<DefiniteReachabilityAnnotation> remove = new LinkedHashSet<>();
        for (final DefiniteReachabilityAnnotation defReach : annotationsForThisState) {
            if (ha.isMaybeExisting(defReach.getTo())) {
                remove.add(defReach);
            }
        }
        annotationsForThisState.removeAll(remove);

        remove.clear();
        for (final DefiniteReachabilityAnnotation defReach : annotationsForThatState) {
            if (ha.isMaybeExisting(defReach.getTo())) {
                remove.add(defReach);
            }
        }
        annotationsForThatState.removeAll(remove);

        final Set<DefiniteReachabilityAnnotation> mergedAnnotations = new LinkedHashSet<>();

        mergedAnnotations.addAll(DefiniteReachabilities.filterDefiniteReachabilityAnnotations(
            newResult.getHeapPositionsB(),
            annotationsForThisState,
            newResult.getHeapPositionsC()));
        mergedAnnotations.addAll(DefiniteReachabilities.filterDefiniteReachabilityAnnotations(
            newResult.getHeapPositionsA(),
            annotationsForThatState,
            newResult.getHeapPositionsC()));

        // add new annotations
        for (final DefiniteReachabilityAnnotation defReach : mergedAnnotations) {
            assert (!mergedState.getHeapAnnotations().isMaybeExisting(defReach.getTo()));
        }
        mergedState.getHeapAnnotations().getDefiniteReachabilities().addAll(mergedAnnotations);

        // throw out useless annotations
        DefiniteReachabilities.gc(mergedState, Collections.<AbstractVariableReference>emptySet());

        PathMerger.addCostsForLostDefReaches(newResult, true);
        PathMerger.addCostsForLostDefReaches(newResult, false);

        // for testing only:
        // newResult.getMergedState().getHeapAnnotations().getDefiniteReachabilities().addAll(annotationsForThisState);
        // newResult.getMergedState().getHeapAnnotations().getDefiniteReachabilities().addAll(annotationsForThatState);
    }

    /**
     * Checks if all reachability annotations in the source states are still represented in the merged state.
     * @param newResult the result being constructed
     * @param checkThis boolean flag indicating if the left (true) or right (false) state are checked.
     * @throws TooExpensiveException if merging is aborted.
     */
    public static void addCostsForLostDefReaches(final JBCMergeResult newResult, final boolean checkThis)
        throws TooExpensiveException
    {
        // is every annotation we have in this state still contained in the resulting state? if not, add costs
        final DefiniteReachabilities mergedAnnotations =
            newResult.getMergedState().getHeapAnnotations().getDefiniteReachabilities();
        final DefiniteReachabilities annotations =
            newResult.getHeapPositions(checkThis).getState().getHeapAnnotations().getDefiniteReachabilities();
        for (final DefiniteReachabilityAnnotation defReach : annotations) {
            final Set<AbstractVariableReference> fromRefList =
                newResult.getVarCache().getResults(defReach.getFrom(), checkThis);
            final Set<AbstractVariableReference> toRefList =
                newResult.getVarCache().getResults(defReach.getTo(), checkThis);
            final Collection<AbstractVariableReference> thisLostRefs = new LinkedList<>();
            thisLostRefs.addAll(fromRefList);
            thisLostRefs.addAll(toRefList);
            if (fromRefList.isEmpty() || toRefList.isEmpty()) {
                if (Globals.DEBUG_RICHARD) {
                    System.err.println("Lost defreach: " + defReach);
                }
                newResult.addCost(
                    CostType.LOST_DEFREACH,
                    Collections.<AbstractVariableReference>emptySet(),
                    thisLostRefs,
                    1,
                    !checkThis);
                continue;
            }
            for (final AbstractVariableReference mergedRefFrom : fromRefList) {
                TOPOS: for (final AbstractVariableReference mergedRefTo : toRefList) {
                    for (final DefiniteReachabilityAnnotation defReachMerged : mergedAnnotations) {
                        if (defReachMerged.getFrom().equals(mergedRefFrom)
                            && defReachMerged.getTo().equals(mergedRefTo)
                            && defReach.getFields().containsAll(defReachMerged.getFields()))
                        {
                            continue TOPOS;
                        }
                    }
                    /*
                     * If we arrive here, we had an annotation in this state without a corresponding annotation in the
                     * merged state. Add costs!
                     */
                    if (Globals.DEBUG_RICHARD) {
                        System.err.println("Lost defreach: " + defReach);
                    }
                    newResult.addCost(
                        CostType.LOST_DEFREACH,
                        Collections.<AbstractVariableReference>emptySet(),
                        thisLostRefs,
                        1,
                        !checkThis);
                }
            }
        }
    }

    /**
     * Merges (recursively) two abstract arrays.
     * @param thisState one of the two involved states
     * @param thatState the other involved state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @param mergedType the merged type information
     * @throws TooExpensiveException if merging is aborted.
     * @return an array that is the merged result of thisVarRef and thatVarRef
     */
    private static AbstractVariableReference mergeArrays(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos,
        final AbstractType mergedType) throws TooExpensiveException
    {
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);
        final AbstractVariable thisVar = thisState.getAbstractVariable(thisVarRef);
        final AbstractVariable thatVar = thatState.getAbstractVariable(thatVarRef);
        final State mergedState = newResult.getMergedState();

        final AbstractVariableReference resRef;

        if (thisVar instanceof Array && thatVar instanceof Array) {

            // take care of the abstract array lengths
            final StatePosition lengthPos = pos.appendArrayLength();
            final AbstractVariableReference mergedArrayLengthRef =
                PathMerger.mergeVariableReferences(thisState, thatState, newResult, lengthPos);
            final AbstractInt mergedArrayLength = (AbstractInt) mergedState.getAbstractVariable(mergedArrayLengthRef);

            /*
             * Only way to keep a concrete array: Both merge partners are
             * concrete arrays and their length is the same:
             */
            if (thisVar instanceof ConcreteArray && thatVar instanceof ConcreteArray && mergedArrayLength.isLiteral()) {

                final ConcreteArray mergedArray = new ConcreteArray(mergedArrayLengthRef, mergedState, null);

                resRef = mergedState.createReferenceAndAdd(mergedArray, OperandType.ARRAY);
                /*
                 * We need to store here, so that we stop traversing the heap
                 * in case of recursive structures. Only if we add (x,y)->z
                 * here, we can stop when we encounter (x,y) again.
                 */
                newResult.store(thisVarRef, thatVarRef, resRef, pos);

                // merge the references contained in the arrays
                for (int index = 0; index < mergedArrayLength.getLiteral().intValue(); index++) {
                    final StatePosition newPos = pos.appendArrayElement(index);
                    final AbstractVariableReference mergedRef =
                        PathMerger.mergeVariableReferences(thisState, thatState, newResult, newPos);
                    mergedArray.put(index, mergedRef);
                }
            } else {
                if (thisVar instanceof ConcreteArray) {
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
                } else if (thatVar instanceof ConcreteArray) {
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
                }
                //All needed structure information will be fixed in mergeAnnotations
                final AbstractArray mergedArray = new AbstractArray(mergedArrayLengthRef);
                resRef = mergedState.createReferenceAndAdd(mergedArray, OperandType.ARRAY);
            }
        } else {
            if (thisVar instanceof Array) {
                newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
            } else {
                newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
            }
            // we need to restrict to the most common "slice": java.lang.Object
            final ConcreteInstance res = ConcreteInstance.newJLO(mergedState);
            resRef = mergedState.createReferenceAndAdd(res, OperandType.ADDRESS);
        }
        mergedState.setAbstractType(resRef, mergedType);

        return resRef;
    }

    /**
     * Just carry over the cyclic annotations according to Def. 2k.
     * @param newResult the result being constructed
     * @param isThisState true iff this is the "left" state
     * @throws TooExpensiveException if merging is aborted
     */
    private static void mergeCyclicAnnotations(final JBCMergeResult newResult, final boolean isThisState)
        throws TooExpensiveException
    {
        final HeapPositions heapPositions = newResult.getHeapPositions(isThisState);
        final State state = heapPositions.getState();

        final CyclicStructures thisCyclic = state.getHeapAnnotations().getCyclicStructures();

        for (final AbstractVariableReference ref : thisCyclic.getCyclicRefs()) {
            final ImmutableSet<HeapEdge> neededE = thisCyclic.getNeededEdgesOf(ref);

            /*
             * The reference is marked as possibly cyclic, so mark all
             * corresponding positions (or the maximum prefix) as possibly
             * cyclic in the merged state, too.
             */
            for (final StatePosition pos : heapPositions.getPositionsForRef(ref)) {
                PathMerger.setCyclic(newResult, pos, neededE, isThisState);
            }
        }
    }

    /**
     * Merges (recursively) two non-primitive abstract and existing instances.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @param mergedType the merged type information
     * @throws TooExpensiveException if merging is aborted.
     * @return a non-primitive that is the merged result of thisVarRef and
     * thatVarRef
     */
    private static AbstractVariableReference mergeExistingReferences(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos,
        final AbstractType mergedType) throws TooExpensiveException
    {

        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);
        AbstractVariableReference resRef = null;

        final AbstractVariable varThis = thisState.getAbstractVariable(thisVarRef);
        final AbstractVariable varThat = thatState.getAbstractVariable(thatVarRef);

        /*
         * When we now merge the references x+y and we find that there already is a merge partner with realized fields
         * for x that is not y (or vice versa), we do not want to continue merging by following through the fields of x
         * and y.
         * As a consequence, we take a look at the VarCache here and ignore the "good" information about some existing
         * object so that we introduce an abstract instance with just the information "is existing" in the merge result.
         * Here we also need to take care that we merge the type information.
         */

        final VariableCache varCache = newResult.getVarCache();
        final Set<AbstractVariableReference> rightPartners = varCache.getPartnersForLeft(thisVarRef);
        final Set<AbstractVariableReference> rightRealizedPartners = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : rightPartners) {
            if (ref.isNULLRef()) {
                continue;
            }
            final AbstractVariable rightVal = thatState.getAbstractVariable(ref);
            if (rightVal != null
                && rightVal instanceof ConcreteInstance
                && !((ConcreteInstance) rightVal).isOnlyRealizedUpToJLO())
            {
                rightRealizedPartners.add(ref);
            }
            if (rightVal != null && rightVal instanceof Array) {
                rightRealizedPartners.add(ref);
            }
        }
        final Set<AbstractVariableReference> leftPartners = varCache.getPartnersForRight(thatVarRef);
        final Set<AbstractVariableReference> leftRealizedPartners = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : leftPartners) {
            if (ref.isNULLRef()) {
                continue;
            }
            final AbstractVariable leftVal = thisState.getAbstractVariable(ref);
            if (leftVal != null
                && leftVal instanceof ConcreteInstance
                && !((ConcreteInstance) leftVal).isOnlyRealizedUpToJLO())
            {
                leftRealizedPartners.add(ref);
            }
            if (leftVal != null && leftVal instanceof Array) {
                leftRealizedPartners.add(ref);
            }
        }
        final boolean needToAbstract = !leftRealizedPartners.isEmpty() || !rightRealizedPartners.isEmpty();

        boolean abstractPredecessor = false;
        if (needToAbstract && !newResult.onlyFindInstance()) {
            /*
             * In case of realized cycles, there might be situations where we could continue the merge process without
             * needing to abstract anything (by introducing possible equality between realized instances). This can be
             * observed with ListInt.append().
             *
             * We want to abstract after a finite time. Because using possible equality between realized instances is
             * useful for all java.util.LinkedList examples, we use more refined heuristics.
             *
             * Whenever we merge two references at some position, where we for both states already had an (possibly)
             * identical predecessor, we do not want to finish this particular merge. Instead, we enforce abstraction of
             * the predecessor.
             */
            final AbstractVariableReference refThis = thisState.getReference(pos);
            final AbstractVariableReference refThat = thatState.getReference(pos);
            boolean repetitionThis = false;
            boolean repetitionThat = false;
            for (final StatePosition prefix : pos.getPathToRoot()) {
                if (prefix == pos) {
                    continue;
                }
                final AbstractVariableReference prefixRefThis = thisState.getReference(prefix);
                if (refThis.equals(prefixRefThis)
                    || thisState
                        .getHeapAnnotations()
                        .getEqualityGraph()
                        .areMarkedAsPossiblyEqual(prefixRefThis, refThis))
                {
                    repetitionThis = true;
                }
                final AbstractVariableReference prefixRefThat = thatState.getReference(prefix);
                if (refThat.equals(prefixRefThat)
                    || thatState
                        .getHeapAnnotations()
                        .getEqualityGraph()
                        .areMarkedAsPossiblyEqual(prefixRefThat, refThat))
                {
                    repetitionThat = true;
                }
                if (repetitionThis && repetitionThat) {
                    abstractPredecessor = true;
                    break;
                }
            }
        }

        if (needToAbstract) {
            /*
             * We do not want to have very detailled information in order to have a finite representation of the heap.
             * Here we either abstract to just java.lang.Object (meaning: the object exists) or maybe keep some field
             * information that just points to non-abstracted parts of thea heap.
             */
            resRef = new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);

            newResult.getMergedState().setAbstractType(resRef, mergedType);

            // the actual work is done later when we know the complete heap structure in the merged state
            newResult.getForcedAbstractions().add(resRef);
        } else {
            if (varThis instanceof ObjectInstance && varThat instanceof ObjectInstance) {
                //  no array involved
                resRef = PathMerger.mergeInstances(thisState, thatState, newResult, pos, mergedType);
            } else if (varThis instanceof Array || varThat instanceof Array) {
                // at least one array involved
                resRef = PathMerger.mergeArrays(thisState, thatState, newResult, pos, mergedType);
            } else {
                assert (false);
            }
        }
        assert (resRef != null);

        if (abstractPredecessor) {
            assert (pos instanceof NonRootPosition);
            final StatePosition predPos = ((NonRootPosition) pos).getPrev();
            final AbstractVariableReference predRefThis = thisState.getReference(predPos);
            final AbstractVariableReference predRefThat = thatState.getReference(predPos);
            final AbstractVariableReference predRef = newResult.getMergedReference(predRefThis, predRefThat);

            // the actual work is done later when we know the complete heap structure in the merged state
            newResult.getForcedAbstractionsSuccessors().add(resRef);
            newResult.getForcedAbstractions().add(predRef);
            return resRef;
        }

        return resRef;
    }

    /**
     * Merge two individual stack frames.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param frameNum the position of the stack frames to be merged
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeFrames(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final int frameNum) throws TooExpensiveException
    {
        final StackFrame thisSF = thisState.getCallStack().get(frameNum);
        final StackFrame thatSF = thatState.getCallStack().get(frameNum);
        final StackFrame mergedSF = newResult.getMergedState().getCallStack().get(frameNum);
        if (!thisSF.getCurrentOpCode().equals(thatSF.getCurrentOpCode())) {
            if (Globals.DEBUG_COTTO) {
                throw new TooExpensiveException("OpCodes differ:\n" + thisSF + "\n" + thatSF);
            } else {
                throw new TooExpensiveException("OpCodes differ:");
            }

        }

        // Both or none must have a thrown exception:
        if (thisSF.hasException() != thatSF.hasException()) {
            throw new TooExpensiveException("Difference in thrown exceptions.");
        }

        PathMerger.mergeInputReferences(thisState, thatState, newResult, frameNum);

        PathMerger.mergeLocalVariables(thisState, thatState, newResult, frameNum);

        PathMerger.mergeOperandStacks(thisState, thatState, newResult, frameNum);

        // Now also have a look at the thrown exceptions
        if (thisSF.hasException() && thatSF.hasException()) {
            final StatePosition pos = ExceptionRootPosition.create(frameNum);
            mergedSF.setException(PathMerger.mergeVariableReferences(thisState, thatState, newResult, pos));
        }
    }

    /**
     * Merges (recursively) two abstract instances.
     * @param thisState the state containing thisVar
     * @param thatState the state containing thatVar
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @param mergedType the merged type information
     * @throws TooExpensiveException if merging is aborted.
     * @return an instance that is the merged result of thisVarRef and
     * thatVarRef
     */
    private static AbstractVariableReference mergeInstances(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos,
        final AbstractType mergedType) throws TooExpensiveException
    {
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);
        final AbstractVariable thisV = thisState.getAbstractVariable(thisVarRef);
        final AbstractVariable thatV = thatState.getAbstractVariable(thatVarRef);
        assert (thisV instanceof ObjectInstance);
        assert (thatV instanceof ObjectInstance);

        final State mergedState = newResult.getMergedState();
        final AbstractVariableReference resRef;
        if (thisV instanceof ConcreteInstance && thatV instanceof ConcreteInstance) {
            final ConcreteInstance thisVar = (ConcreteInstance) thisV;
            final ConcreteInstance thatVar = (ConcreteInstance) thatV;

            /*
             * Only create explicit information up to the type that is realized in
             * both instances.
             */
            final TypeTree thisRealizedType = thisVar.getMostSpecializedInstance().getType();
            final TypeTree thatRealizedType = thatVar.getMostSpecializedInstance().getType();
            TypeTree maxCommonRealizedType = thisRealizedType.getMaxCommonSupertype(thatRealizedType);

            /*
             * We want to make sure that there is at least one field in the maxCommonRealizedType which exists in both
             * thisVar and thatVar. Think about merging Something(a=?, b=null) and Something(a=null, b=?). If there is
             * no such field, we want to drop the corresponding slice. However, if we are dealing with a class that
             * _has_ no fields, we must not abstract (and add costs).
             */
            TypeTree current = maxCommonRealizedType;
            while (current != null) {
                final ConcreteInstance sliceThis = thisVar.getConcreteInstanceSliceAtType(current);
                final ConcreteInstance sliceThat = thatVar.getConcreteInstanceSliceAtType(current);
                final Set<String> fieldsThis = sliceThis.getFields().keySet();
                final Set<String> fieldsThat = sliceThat.getFields().keySet();
                if (fieldsThis.isEmpty() && fieldsThat.isEmpty()) {
                    // there is no field in this slice, which is OK!
                    break;
                } else {
                    final Set<String> intersection = new LinkedHashSet<>(fieldsThis);
                    intersection.retainAll(fieldsThat);
                    if (intersection.isEmpty()) {
                        maxCommonRealizedType = current.getSuperType();
                    }
                }

                if (current.getSuperType() == null) {
                    maxCommonRealizedType = current;
                }
                current = current.getSuperType();
            }

            // We may have lost some information, so add costs
            TypeTree currentThisType = thisRealizedType;
            while (currentThisType != maxCommonRealizedType) {
                newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
                currentThisType = currentThisType.getSuperType();
            }

            TypeTree currentThatType = thatRealizedType;
            while (currentThatType != maxCommonRealizedType) {
                newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
                currentThatType = currentThatType.getSuperType();
            }

            /*
             * Create a new instance of the now decided type. This will be used
             * as the container for the merged fields which are added later.
             */
            final ConcreteInstance res =
                ConcreteInstance.newInstanceFromType(mergedState, maxCommonRealizedType, FieldValueSettings.NULL_VALUE);

            // Already add it to the new state
            resRef = mergedState.createReferenceAndAdd(res, OperandType.ADDRESS);
            mergedState.setAbstractType(resRef, mergedType);

            /*
             * We need to store here, so that we stop traversing the heap in case of
             * recursive structures. Only if we add (x,y)->z here, we can stop when
             * we encounter (x,y) again.
             */
            newResult.store(thisVarRef, thatVarRef, resRef, pos);

            /*
             * Run through all all fields (in all "boxes" of our object notation) of
             * the new object, while doing the same on the pre-existing objects.
             */
            TypeTree curType = maxCommonRealizedType;
            while (curType != null) {
                final ConcreteInstance mergedSlice = res.getConcreteInstanceSliceAtType(curType);
                final ConcreteInstance thisSlice = thisVar.getConcreteInstanceSliceAtType(curType);
                final ConcreteInstance thatSlice = thatVar.getConcreteInstanceSliceAtType(curType);
                assert (thisSlice != null && thatSlice != null);

                //Don't allowing merging of refs with cycle joint with those that have none:
                if (curType.getClassName().equals(ClassName.Important.JAVA_LANG_OBJECT.getClassName())) {
                    //They should both be empty for all normal objects:
                    if (!thisSlice.getFields().keySet().equals(thatSlice.getFields().keySet())) {
                        newResult.addCost(CostType.LOST_CYCLEJOINT, thisVarRef, thatVarRef, true);
                    }
                }

                // merge all fields in this slice
                final List<String> commonFields = new ArrayList<>();
                final Set<String> fieldsThis = thisSlice.getFields().keySet();
                final Set<String> fieldsThat = thatSlice.getFields().keySet();

                commonFields.addAll(fieldsThis);
                commonFields.retainAll(fieldsThat);

                if (!commonFields.containsAll(fieldsThis)) {
                    // a field is missing in thatState
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
                }
                if (!commonFields.containsAll(fieldsThat)) {
                    // a field is missing in thisState
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
                }
                for (final String name : commonFields) {
                    final StatePosition newPos = pos.appendField(new FieldIdentifier(curType.getClassName(), name));
                    final AbstractVariableReference mergedRef =
                        PathMerger.mergeVariableReferences(thisState, thatState, newResult, newPos);
                    mergedSlice.setField(name, mergedRef);
                }
                curType = curType.getSuperType();
            }
        } else {
            //In the case that one of the instances was abstract, we generate an
            //abstract one:
            resRef = mergedState.createReferenceAndAdd(new AbstractInstance(), OperandType.ADDRESS);
            mergedState.setAbstractType(resRef, mergedType);

            // add cost
            if (thisV instanceof ConcreteInstance) {
                assert (thatV instanceof AbstractInstance);
                newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
            } else if (thatV instanceof ConcreteInstance) {
                assert (thisV instanceof AbstractInstance);
                newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
            }
        }
        return resRef;
    }

    /**
     * Merge the local variable arrays of the two stack frames.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param frameNum the position of the stack frames to be merged
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeLocalVariables(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final int frameNum) throws TooExpensiveException
    {
        final StackFrame thisSF = thisState.getCallStack().get(frameNum);
        final StackFrame thatSF = thatState.getCallStack().get(frameNum);
        final StackFrame mergedSF = newResult.getMergedState().getCallStack().get(frameNum);

        /*
         * Both copies have equal length (the length is derived from the OpCode,
         * which both share)
         */
        for (final int varNum : thisSF.getActiveVariables()) {
            final AbstractVariableReference thisRef = thisSF.getLocalVariable(varNum);
            final AbstractVariableReference thatRef = thatSF.getLocalVariable(varNum);
            if (thisRef != null && thatRef != null) {
                // This local variable is in use in both stack frames:
                final StatePosition pos = LocVarRootPosition.create(frameNum, varNum);
                final AbstractVariableReference newRef = PathMerger.mergeVariableReferences(thisState, thatState, newResult, pos);

                mergedSF.setLocalVariable(varNum, newRef);
            } else {
                /*
                 * TODO
                 * For non-complete (but sound) used variable analyses, the
                 * check thisRef == thatRef can fail. Because we are dealing
                 * with verified bytecode, we can assume the variable indeed
                 * is not used at this position. This, however, must also be
                 * reflected in the nodes connected to the nodes we could safely
                 * modify here. As a consequence, this is left for future work.
                 */
                assert (thisRef != thatRef);

                // Both variable indices unused: That one's easy!
                continue;
            }
        }
    }

    /**
     * Merges (recursively) two non-primitive abstract values.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @param mergedType the merged type information
     * @throws TooExpensiveException if merging is aborted.
     * @return a non-primitive that is the merged result of thisVarRef and
     * thatVarRef
     */
    private static AbstractVariableReference mergeMaybeExisting(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos,
        final AbstractType mergedType) throws TooExpensiveException
    {
        JBCOptions options = thisState.getJBCOptions();
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);

        final AbstractVariableReference resRef;
        final State mergedState = newResult.getMergedState();

        resRef = PathMerger.getNewNonPrimitiveVarRef(thisVarRef, thatVarRef);
        mergedState.getHeapAnnotations().setMaybeExisting(resRef);
        mergedState.setAbstractType(resRef, mergedType);

        // We need to add costs, if exactly one instance was known to exist.
        if (thisState.getHeapAnnotations().isMaybeExisting(thisVarRef)
            && !thatState.getHeapAnnotations().isMaybeExisting(thatVarRef))
        {
            /*
             * The instance may exist in thisState, but exists for sure in
             * thatState.
             */
            if (!thatVarRef.equals(newResult.getReplacementReference())) {
                boolean isRealized = thisState.getAbstractVariable(thisVarRef) instanceof ConcreteInstance
                        || thatState.getAbstractVariable(thatVarRef) instanceof ConcreteInstance;
                if (isRealized && thisState.getClassPath().typeHasOnlyPrimitiveFields(mergedType, options)) {
                    newResult.addCost(CostType.LOST_SIMPLE_EXISTENCE, thatVarRef, thisVarRef, true);
                } else {
                    newResult.addCost(CostType.LOST_EXISTENCE, thatVarRef, thisVarRef, true);
                }
            }
            final AbstractVariable thatVar = thatState.getAbstractVariable(thatVarRef);
            if (thatVar instanceof ConcreteInstance) {
                for (final FieldIdentifier f : ((ConcreteInstance) thatVar).getAllFields().keySet()) {
                    if (f.getFieldName().endsWith("!cycleJoint")) {
                        newResult.addCost(CostType.LOST_CYCLEJOINT, thatVarRef, thisVarRef, true);
                    }
                }
            }
        } else if (thatState.getHeapAnnotations().isMaybeExisting(thatVarRef)
            && !thisState.getHeapAnnotations().isMaybeExisting(thisVarRef))
        {
            /*
             * The instance may exist in thatState.
             */
            boolean isRealized = thisState.getAbstractVariable(thisVarRef) instanceof ConcreteInstance
                    || thatState.getAbstractVariable(thatVarRef) instanceof ConcreteInstance;
            if (isRealized && thisState.getClassPath().typeHasOnlyPrimitiveFields(mergedType, options)) {
                newResult.addCost(CostType.LOST_SIMPLE_EXISTENCE, thatVarRef, thisVarRef, false);
            } else {
                newResult.addCost(CostType.LOST_EXISTENCE, thatVarRef, thisVarRef, false);
            }
            final AbstractVariable thisVar = thisState.getAbstractVariable(thisVarRef);
            if (thisVar instanceof ConcreteInstance) {
                for (final FieldIdentifier f : ((ConcreteInstance) thisVar).getAllFields().keySet()) {
                    if (f.getFieldName().endsWith("!cycleJoint")) {
                        newResult.addCost(CostType.LOST_CYCLEJOINT, thisVarRef, thatVarRef, true);
                    }
                }
            }
        }
        assert (resRef != null);
        return resRef;
    }

    /**
     * Merges (recursively) two non-primitive abstract values.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @throws TooExpensiveException if merging is aborted.
     * @return a non-primitive that is the merged result of thisVarRef and
     * thatVarRef
     */
    private static AbstractVariableReference mergeNonPrimitives(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos) throws TooExpensiveException
    {
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);
        AbstractVariableReference resRef = null;

        // just merge the type information of both instances
        final AbstractType mergedType = PathMerger.mergeTypeInformation(thisState, thatState, newResult, pos);

        if (thisVarRef.isNULLRef() || thatVarRef.isNULLRef()) {
            // we are merging x + null, null + x, or null + null
            resRef = PathMerger.mergeWithNull(thisState, thatState, newResult, pos, mergedType);
        } else if (thisState.getHeapAnnotations().isMaybeExisting(thisVarRef)
            || thatState.getHeapAnnotations().isMaybeExisting(thatVarRef))
        {
            // at least one of the two instances is marked as maybe existing
            resRef = PathMerger.mergeMaybeExisting(thisState, thatState, newResult, pos, mergedType);
        } else {
            // merge two existing instances
            resRef = PathMerger.mergeExistingReferences(thisState, thatState, newResult, pos, mergedType);

        }
        assert (resRef != null);
        return resRef;
    }

    /**
     * Just carry over the non-tree annotations according to Def. 2j.
     * @param newResult the result being constructed
     * @param isThisState true iff this is the "left" state
     * @throws TooExpensiveException if merging is aborted
     */
    private static void mergeNonTreeAnnotations(final JBCMergeResult newResult, final boolean isThisState)
        throws TooExpensiveException
    {
        final HeapPositions heapPositions = newResult.getHeapPositions(isThisState);

        for (final AbstractVariableReference ref : heapPositions
            .getState()
            .getHeapAnnotations()
            .getPossiblyNonTreeRefs())
        {
            for (final StatePosition pos : heapPositions.getPositionsForRef(ref)) {
                PathMerger.setNonTree(newResult, pos, isThisState);
            }
        }
    }

    /**
     * In the merged state, add a non-tree annotation to all prefixes of pos.
     * Here the prefixes are computed based on fromThisState. If an annotation
     * was added, add costs if that annotation was missing in the other state.
     * @param newResult the result being constructed
     * @param pos the position where the non-tree annotation/shape exists/starts
     * @param fromThisState true if the non-tree annotation/shape exists in this
     * state
     * @throws TooExpensiveException if merging is aborted
     */
    private static void setNonTree(final JBCMergeResult newResult, final StatePosition pos, final boolean fromThisState)
        throws TooExpensiveException
    {
        final HeapPositions mergedHeapPositions = newResult.getHeapPositionsC();
        final HeapPositions heapPositions = newResult.getHeapPositions(fromThisState);
        final State mergedState = newResult.getMergedState();
        final HeapPositions otherHeapPositions = newResult.getHeapPositions(!fromThisState);
        final State otherState = otherHeapPositions.getState();

        for (final AbstractVariableReference mergedRef : mergedHeapPositions.getMaxRealizedReferences(
            pos,
            heapPositions))
        {
            if (!mergedState.getHeapAnnotations().setPossiblyNonTree(mergedRef)) {
                /*
                 * We already marked the reference in the merged state
                 * as non-tree, we do not have to check the other state.
                 *
                 * Strictly speaking this might cause some references to not be
                 * checked, if we lost positions (due to possible equality) and
                 * therefore less Costs are introduced. This, however, is not a
                 * problem, as every loss of positions always introduces costs
                 * (meaning: we do not return false "is an instance" answers).
                 */
                continue;
            }

            for (final AbstractVariableReference otherRef : otherHeapPositions.getMaxRealizedReferences(
                pos,
                heapPositions))
            {
                final AbstractVariableReference thisRef = heapPositions.getReferenceForPos(pos, true);
                if (!otherState.getHeapAnnotations().isPossiblyNonTree(otherRef)) {
                    /*
                     * Even if there is some realized non-tree shape in the
                     * other state, this still does not allow arbitrary non-tree
                     * shapes which are allowed based on the non-tree annotation
                     * in the original state. Therefore, the merged state is not
                     * an instance of the other state and we need to add costs.
                     */
                    newResult.addCost(CostType.LOST_TREE, otherRef, thisRef, fromThisState);
                }
            }
        }
    }

    /**
     * Merge the operand stacks of the two stack frames.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param frameNum the position of the stack frames to be merged
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeOperandStacks(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final int frameNum) throws TooExpensiveException
    {
        final StackFrame thisSF = thisState.getCallStack().get(frameNum);
        final StackFrame thatSF = thatState.getCallStack().get(frameNum);
        final StackFrame mergedSF = newResult.getMergedState().getCallStack().get(frameNum);

        /*
         * Both copies have equal height (the length is derived from the OpCode,
         * which both share)
         */
        final OperandStack thisOpStack = thisSF.getOperandStack();
        final OperandStack thatOpStack = thatSF.getOperandStack();
        assert (thisOpStack.getStack().size() == thatOpStack.getStack().size());

        for (int varNum = 0; varNum < thisOpStack.getStack().size(); varNum++) {
            final StatePosition pos = OpStackRootPosition.create(frameNum, varNum);

            final AbstractVariableReference newRef = PathMerger.mergeVariableReferences(thisState, thatState, newResult, pos);

            mergedSF.getOperandStack().set(varNum, newRef);
        }
    }

    /**
     * Merge two primitives abstract variables, returning a new one representing
     * all values represented by the two abstract variables passed as arguments.
     * @param varA {@link AbstractPrimitive} to merge with varB
     * @param refA the reference to <code>varA</code>
     * @param varB {@link AbstractPrimitive} to merge with varA
     * @param refB the reference to <code>varB</code>
     * @param pos minimal position at which both varA and varB appear.
     * @param newResult the result being constructed
     * @return {@link AbstractPrimitive} representing all values represented by
     * varA and varB (and possibly more)
     * @throws TooExpensiveException if merging is aborted.
     */
    private static AbstractNumber mergePrimitives(
        final AbstractNumber varA,
        final AbstractVariableReference refA,
        final AbstractNumber varB,
        final AbstractVariableReference refB,
        final StatePosition pos,
        final JBCMergeResult newResult) throws TooExpensiveException
    {
        AbstractNumberMergeResult variableMergeResult;
        if (varA instanceof AbstractInt) {
            final AbstractInt intA = (AbstractInt) varA;
            variableMergeResult =
                intA.merge(
                    varB,
                    newResult.getIncreaseCounters(),
                    IntegerType.UNBOUND);
        } else {
            variableMergeResult = ((AbstractFloat) varA).merge(varB);
        }

        newResult.addCost(
            variableMergeResult.getVarAtoMerged(),
            Collections.singleton(refB),
            Collections.singleton(refA),
            JBCMergeResult.getCostFactor(pos),
            false);

        /*
         *  If the second variable (varB) differs from the merged result,
         *  varA is not an instance of varB.
         */
        if (variableMergeResult.getVarBtoMerged() != CostType.NONE) {
            newResult.addCost(
                variableMergeResult.getVarAtoMerged(),
                Collections.singleton(refA),
                Collections.singleton(refB),
                JBCMergeResult.getCostFactor(pos),
                true);
        }

        final CostType wideningCost = variableMergeResult.getEnforcedWideningCost();
        if (wideningCost != null) {
            newResult.addConditionalCost(wideningCost, refA, refB, JBCMergeResult.getCostFactor(pos));
        }

        return variableMergeResult.getMergedVariable();
    }

    /**
     * Merge the stack, that is merge everything inside the stack frames.
     * @param thisState the state corresponding to thisCallStack
     * @param thatState the state corresponding to thatCallStack
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeStacks(final State thisState, final State thatState, final JBCMergeResult newResult)
        throws TooExpensiveException
    {
        final CallStack thisCallStack = thisState.getCallStack();
        final CallStack thatCallStack = thatState.getCallStack();
        final int heightThis = thisCallStack.size();
        final int heightThat = thatCallStack.size();
        if (heightThat != heightThis) {
            throw new TooExpensiveException("stack height differs");
        }

        final State mergedState = newResult.getMergedState();
        final CallStack mergedCallStack = mergedState.getCallStack();

        /*
         * First create the raw structure of the call stack so that the state
         * positions can be used.
         */
        final List<StackFrame> stackFrameList = mergedCallStack.getStackFrameList();
        for (int i = 0; i < heightThis; i++) {
            stackFrameList.add(null);
        }

        // start at the top, because we expect more differences there
        for (int stackPos = 0; stackPos < heightThis; stackPos++) {
            final StackFrame thisSF = thisCallStack.get(stackPos);
            final StackFrame mergedSF =
                new StackFrame(thisSF.getCurrentOpCode(), thisSF.getOperandStack().getStack().size());
            stackFrameList.set(stackPos, mergedSF);
            PathMerger.mergeFrames(thisState, thatState, newResult, stackPos);
        }
    }

    /**
     * Take care that the merged state contains merged values for the static
     * fields.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeStaticFields(final State thisState, final State thatState, final JBCMergeResult newResult)
        throws TooExpensiveException
    {
        final State mergedState = newResult.getMergedState();

        final Collection<ClassName> classes = new LinkedHashSet<>(thisState.getStaticFields().getClasses());
        if (classes.addAll(thatState.getStaticFields().getClasses())) {
            throw new TooExpensiveException("the states do not know the same static fields");
        }

        final ClassPath cPath = thisState.getClassPath();
        for (final ClassName cn : classes) {
            for (final Map.Entry<String, Field> pair : cPath.getClass(cn).getStaticFields().entrySet()) {
                final String fieldName = pair.getKey();
                final StatePosition pos = StaticFieldRootPosition.create(new FieldIdentifier(cn, fieldName));

                final AbstractVariableReference newRef = PathMerger.mergeVariableReferences(thisState, thatState, newResult, pos);
                mergedState.getStaticFields().set(cn, fieldName, newRef);
            }
        }
    }

    /**
     * Merge the types for two abstract variable reference.
     * @param thisState the left state in this merge
     * @param thatState the right state in this merge
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @return class of the merge result of thisVarRef/thatVarRef
     * @throws TooExpensiveException if merging is aborted.
     */
    private static AbstractType mergeTypeInformation(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos) throws TooExpensiveException
    {
        JBCOptions options = thisState.getJBCOptions();
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);

        final ClassPath cPath = thisState.getClassPath();

        final AbstractType thisType = thisState.getAbstractType(thisVarRef);
        final AbstractType thatType = thatState.getAbstractType(thatVarRef);

        if (thisType == null) {
            return thatType;
        }
        if (thatType == null) {
            return thisType;
        }
        if (thisType.equals(thatType)) {
            return thisType;
        }

        final AbstractType newType = AbstractType.union(cPath, options, thisType, thatType);

        //Check if this led to any new types:
        if (!thisType.containsAll(newType, cPath, options)) {
            newResult.addCost(CostType.LOST_TYPEINFO, thisVarRef, thatVarRef, false);
        }
        if (!thatType.containsAll(newType, cPath, options)) {
            newResult.addCost(CostType.LOST_TYPEINFO, thatVarRef, thisVarRef, true);
        }

        return newType;
    }

    /**
     * Merge two references to abstract variables, returning a new one
     * referencing an abstract variable representing all values represented by
     * the two input references.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @return {@link AbstractVariableReference} to the merged
     * {@link AbstractVariable} (which has already been added to the merged
     * state).
     * @throws TooExpensiveException if merging is aborted.
     */
    private static AbstractVariableReference mergeVariableReferences(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos) throws TooExpensiveException
    {
        final AbstractVariableReference refA = thisState.getReference(pos);
        final AbstractVariableReference refB = thatState.getReference(pos);
        if (refA == null || refB == null) {
            throw new TooExpensiveException("one of the positions is not valid in one of the states");
        }

        final State mergedState;

        // do we already know the result?
        AbstractVariableReference resRef = newResult.getMergedReference(refA, refB);
        if (resRef != null) {
            // FIXME add flag
            if (!refA.pointsToConstantInt() || !refB.pointsToConstantInt() || refA.equals(refB)) {
                if (Globals.useAssertions) {
                    mergedState = newResult.getMergedState();
                    assert (newResult.getForcedAbstractions().contains(resRef)
                        || mergedState.getAbstractVariable(resRef) != null
                        || resRef.isNULLRef()
                        || mergedState.getHeapAnnotations().isMaybeExisting(resRef) || resRef instanceof ReturnAddress);
                }
                return resRef;
            }
        }
        mergedState = newResult.getMergedState();

        if (refA instanceof ReturnAddress || refB instanceof ReturnAddress) {
            /*
             * A return address exists when the JSR/RET opcodes are used.
             * Because different values correspond to different paths through
             * the code, we do not merge the values. This is not a problem,
             * because we only have finitely many return addresses.
             */
            assert (refA instanceof ReturnAddress && refB instanceof ReturnAddress);
            if (!refA.equals(refB)) {
                throw new TooExpensiveException("Different Return Addresses");
            }
            resRef = refA;
        } else {
            final AbstractVariable varA = thisState.getAbstractVariable(refA);
            final AbstractVariable varB = thatState.getAbstractVariable(refB);

            // Are these primitive values?
            if (varA instanceof AbstractNumber || varB instanceof AbstractNumber) {
                assert (varA instanceof AbstractNumber && varB instanceof AbstractNumber);
                final AbstractNumber newVar =
                    PathMerger.mergePrimitives((AbstractNumber) varA, refA, (AbstractNumber) varB, refB, pos, newResult);
                if (newVar.equals(varA) && newVar.equals(varB) && refA.equals(refB)) {
                    // nothing changed, no need to create a new reference
                    resRef = refB;
                    mergedState.addAbstractVariable(resRef, newVar);
                } else {
                    resRef = mergedState.createReferenceAndAdd(newVar, refA.getPrimitiveType());
                }
            } else {
                resRef = PathMerger.mergeNonPrimitives(thisState, thatState, newResult, pos);
            }
        }
        assert (resRef != null);
        if (!(refA.pointsToConstantInt() && refB.pointsToConstantInt() && !refA.equals(refB) && newResult
            .getMergedReference(refA, refB) != null))
        {
            newResult.store(refA, refB, resRef, pos);
        }
        return resRef;
    }

    /**
     * Handle all the cases where at least one variable is the null reference.
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param pos merge the references at this position
     * @param mergedType the merged type information
     * @throws TooExpensiveException if merging is aborted.
     * @return a non-primitive that is the merged result of thisVarRef and
     * thatVarRef
     */
    private static AbstractVariableReference mergeWithNull(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final StatePosition pos,
        final AbstractType mergedType) throws TooExpensiveException
    {
        final AbstractVariableReference thisVarRef = thisState.getReference(pos);
        final AbstractVariableReference thatVarRef = thatState.getReference(pos);

        final State mergedState = newResult.getMergedState();
        AbstractVariableReference resRef;
        // Both instances are the null pointer:
        if (thisVarRef.isNULLRef() && thatVarRef.isNULLRef()) {
            return AbstractVariableReference.NULLREF;
        }
        /*
         * One object is the null pointer. Create a new object with the type of
         * the non-null object, without any actual values for attributes. The
         * latter is needed to ensure the finiteness of the evaluation graph
         * (standard example: List iteration, keeping a pointer to the start
         * value).
         */
        if (thisVarRef.isNULLRef()) {
            resRef = PathMerger.getNewNonPrimitiveVarRef(thisVarRef, thatVarRef);
            mergedState.setAbstractType(resRef, mergedType);
            newResult.addCost(CostType.LOST_NONEXISTENCE, thisVarRef, thatVarRef, false);
            if (!thatState.getHeapAnnotations().isMaybeExisting(thatVarRef)) {
                // thatVar exists!
                newResult.addCost(CostType.LOST_EXISTENCE, thatVarRef, thisVarRef, true);
            }
        } else {
            resRef = PathMerger.getNewNonPrimitiveVarRef(thisVarRef, thatVarRef);
            mergedState.setAbstractType(resRef, mergedType);
            boolean addCost = true;
            final AbstractVariableReference replacementRef = newResult.getReplacementReference();
            if (replacementRef != null) {
                /*
                 * replacementRef.f....g = x? but replacedRef -><- x is
                 * missing, so x is set to null.
                 * Thus, we search for all connections from replacementRef to
                 * x and see if the joins annotations from replacedRef to x
                 * allow it.
                 */
                final HeapPositions thisHeapPos = newResult.getHeapPositionsA();
                final JoiningStructures thisJoins = thisState.getHeapAnnotations().getJoiningStructures();
                for (final StatePosition replacementPos : thisHeapPos.getPositionsForRef(replacementRef)) {
                    for (final StatePosition thisVarPos : thisHeapPos.getPositionsForRef(thisVarRef)) {
                        if (replacementPos.isPrefixOf(thisVarPos)) {
                            if (!thisJoins.areJoining(newResult.getReplacedRef(), thisVarRef)) {
                                addCost = false;
                            }
                        }
                    }
                }
            }
            if (addCost) {
                newResult.addCost(CostType.LOST_NONEXISTENCE, thatVarRef, thisVarRef, true);
            }
            if (!thatState.getHeapAnnotations().isMaybeExisting(thisVarRef)) {
                // thisVar exists!
                newResult.addCost(CostType.LOST_EXISTENCE, thisVarRef, thatVarRef);
            }
        }
        mergedState.getHeapAnnotations().setMaybeExisting(resRef);
        return resRef;
    }

    /**
     * Mark the given position as 'possibly cyclic' with the additional
     * information about needed edges. If any an annotations is missing in the
     * (prefixes of) the other state, add costs.
     * @param neededE the edges defining the maybe cyclic annotation
     * @param pos the position of mergedRef in the merged state
     * @param newResult the result being constructed
     * @param isThisState true if the state that already has the cycle (or the
     * cycle annotation) is this state
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void setCyclic(
        final JBCMergeResult newResult,
        final StatePosition pos,
        final Collection<HeapEdge> neededE,
        final boolean isThisState) throws TooExpensiveException
    {

        final HeapPositions heapPositions = newResult.getHeapPositions(isThisState);
        final HeapPositions otherHeapPositions = newResult.getHeapPositions(!isThisState);
        final State otherState = otherHeapPositions.getState();

        final HeapPositions mergedHeapPositions = newResult.getHeapPositionsC();
        final AbstractVariableReference thisRef = mergedHeapPositions.getReferenceForPos(pos, true);
        final State mergedState = newResult.getMergedState();

        for (final AbstractVariableReference mergedRef : mergedHeapPositions.getMaxRealizedReferences(
            pos,
            heapPositions))
        {
            assert (mergedState.getHeapAnnotations().isPossiblyNonTree(mergedRef)) : "Why is this missing?";

            if (!mergedState.getHeapAnnotations().setPossiblyCyclic(mergedRef, neededE)) {
                continue;
            }

            final CyclicStructures otherCyclic = otherState.getHeapAnnotations().getCyclicStructures();

            for (final AbstractVariableReference refOther : otherHeapPositions.getMaxRealizedReferences(
                pos,
                heapPositions))
            {
                /*
                 * We do not need to add any cost if there is no difference in the
                 * cyclic annotation (it exists and the set of needed edges is small
                 * enough).
                 */
                if (!otherCyclic.isCyclic(refOther) || !neededE.containsAll(otherCyclic.getNeededEdgesOf(refOther))) {
                    newResult.addCost(CostType.LOST_CYCLE_INFORMATION, thisRef, refOther, isThisState);
                }
            }
        }
    }

    /**
     * Start merging the two states provided in the given new result
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result to be constructed
     * @return true iff the given state resulted in a better result (or a
     * feasible result, if no result existed before).
     */
    @Override
    protected boolean computeResult(final State thisState, final State thatState, final JBCMergeResult newResult) {
        try {
            JBCMergerSkeleton.mergeInitialization(thisState, thatState, newResult);

            PathMerger.refineReversibleVoodoo(thisState, thatState, newResult);
            PathMerger.mergeStaticFields(thisState, thatState, newResult);
            PathMerger.mergeStacks(thisState, thatState, newResult);

            PathMerger.abstractInstances(thisState, thatState, newResult);

            PathMerger.mergeAnnotations(thisState, thatState, newResult);

            /* For all relations from thisState, check if they hold in thatState,
             * then add them to the result. */
            PathMerger.mergeIntegerRelations(thisState, thatState, newResult);
            PathMerger.mergeIntegerRelations(thatState, thisState, newResult);

            PathMerger.mergeConstantStringsAndClassInstances(newResult, true);
            PathMerger.mergeConstantStringsAndClassInstances(newResult, false);
        } catch (final TooExpensiveException e) {
            return false;
        }

        /*
         * If we abstracted some instances containing references that are now unreachable, just delete them (which is a
         * partial gc()).
         */
        if (!newResult.getLostReferences().isEmpty()) {
            final Set<AbstractVariableReference> refs = newResult.getMergedState().getReferences().keySet();
            for (final AbstractVariableReference lostRef : newResult.getLostReferences()) {
                if (!refs.contains(lostRef)) {
                    newResult.getMergedState().getHeapAnnotations().justRemove(lostRef);
                }
            }
        }

        return newResult.isValid();
    }

    private static void mergeConstantStringsAndClassInstances(JBCMergeResult newResult, boolean fromLeft) throws TooExpensiveException {
        State thisState = newResult.getHeapPositions(fromLeft).getState();
        State thatState = newResult.getHeapPositions(!fromLeft).getState();
        VariableCache varCache = newResult.getVarCache();
        State mergedState = newResult.getMergedState();
        for (Entry<AbstractVariableReference, String> e: thisState.getConcreteStrings().entrySet()) {
            AbstractVariableReference ref = e.getKey();
            String s = e.getValue();
            for (AbstractVariableReference partner: varCache.getPartners(ref, true)) {
                String partnerString = thatState.getConcreteString(partner);
                if (partnerString == s || (partnerString != null && partnerString.equals(s))) {
                    AbstractVariableReference res = varCache.get(ref, partner);
                    if (res != null) {
                        mergedState.setConcreteString(res, s);
                    }
                } else {
                    if (fromLeft) {
                        newResult.addCost(CostType.LOST_CONCRETE_STRING, ref, partner);
                    } else {
                        newResult.addCost(CostType.LOST_CONCRETE_STRING, ref, partner);
                    }
                }
            }
        }
        for (Entry<AbstractVariableReference, FuzzyType> e: thisState.getClassInstances().entrySet()) {
            AbstractVariableReference ref = e.getKey();
            FuzzyType c = e.getValue();
            for (AbstractVariableReference partner: varCache.getPartners(ref, true)) {
                FuzzyType partnerClass = thatState.getClassInstance(partner);
                if (partnerClass == c || (partnerClass != null && partnerClass.equals(c))) {
                    AbstractVariableReference res = varCache.get(ref, partner);
                    if (res != null) {
                        mergedState.setClassInstance(res, c);
                    }
                } else {
                    if (fromLeft) {
                        newResult.addCost(CostType.LOST_CLASS_INSTANCE, ref, partner);
                    } else {
                        newResult.addCost(CostType.LOST_CLASS_INSTANCE, ref, partner);
                    }
                }
            }
        }
    }

    /**
     * For some references we want to enforce abstraction. Do this here.
     * @param thisState the state corresponding to thisCallStack
     * @param thatState the state corresponding to thatCallStack
     * @param newResult the result being constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void abstractInstances(final State thisState, final State thatState, final JBCMergeResult newResult)
        throws TooExpensiveException
    {
        final ClassPath cPath = thisState.getClassPath();
        final State mergedState = newResult.getMergedState();
        for (final AbstractVariableReference resRef : newResult.getForcedAbstractions()) {
            AbstractVariableReference thisVarRef = null;
            AbstractVariableReference thatVarRef = null;
            for (final Entry<Pair<AbstractVariableReference, AbstractVariableReference>, AbstractVariableReference> entry : newResult
                .getVarCache()
                .getEntrySet())
            {
                if (entry.getValue().equals(resRef)) {
                    thisVarRef = entry.getKey().x;
                    thatVarRef = entry.getKey().y;
                    break;
                }
            }
            assert (thisVarRef != null);
            assert (thatVarRef != null);
            final AbstractVariable varThis = thisState.getAbstractVariable(thisVarRef);
            final AbstractVariable varThat = thatState.getAbstractVariable(thatVarRef);

            /*
             * We only want to abstract the instances because we need a finite representation. However, for some fields
             * we may know that the target reference is already part of our merged state. Therefore, we still represent
             * these fields.
             */
            final Map<FieldIdentifier, Pair<AbstractVariableReference, AbstractVariableReference>> commonFields =
                new LinkedHashMap<>();
            boolean lostFieldThis = false;
            boolean lostFieldThat = false;
            if (varThis instanceof ConcreteInstance && varThat instanceof ConcreteInstance) {
                final ConcreteInstance instanceThis = (ConcreteInstance) varThis;
                final ConcreteInstance instanceThat = (ConcreteInstance) varThat;
                final Map<FieldIdentifier, AbstractVariableReference> fieldsThis = instanceThis.getAllFields();
                final Map<FieldIdentifier, AbstractVariableReference> fieldsThat = instanceThat.getAllFields();
                for (final Entry<FieldIdentifier, AbstractVariableReference> entry : fieldsThis.entrySet()) {
                    final AbstractVariableReference referencedInThat = fieldsThat.get(entry.getKey());
                    if (referencedInThat != null) {
                        commonFields.put(entry.getKey(), new Pair<>(entry.getValue(), referencedInThat));
                    }
                }

                final Iterator<Entry<FieldIdentifier, Pair<AbstractVariableReference, AbstractVariableReference>>> it =
                    commonFields.entrySet().iterator();
                while (it.hasNext()) {
                    final Entry<FieldIdentifier, Pair<AbstractVariableReference, AbstractVariableReference>> entry =
                        it.next();
                    final Pair<AbstractVariableReference, AbstractVariableReference> pair = entry.getValue();
                    final AbstractVariableReference refLeft = pair.x;
                    final AbstractVariableReference refRight = pair.y;

                    final AbstractVariableReference mergedRef = newResult.getVarCache().get(refLeft, refRight);
                    if (mergedRef == null || newResult.getForcedAbstractionsSuccessors().contains(mergedRef)) {
                        it.remove();
                    }
                }

                // Maybe we keep all fields? if so, we are not allowed to add costs!
                for (final Entry<FieldIdentifier, AbstractVariableReference> entry : fieldsThis.entrySet()) {
                    if (entry.getValue() == null) {
                        continue;
                    }
                    final AbstractVariableReference referencedInThat = fieldsThat.get(entry.getKey());
                    if (referencedInThat == null
                        || !new Pair<>(entry.getValue(), referencedInThat).equals(commonFields.get(entry.getKey())))
                    {
                        lostFieldThis = true;
                        break;
                    }
                }

                for (final Entry<FieldIdentifier, AbstractVariableReference> entry : fieldsThat.entrySet()) {
                    if (entry.getValue() == null) {
                        continue;
                    }
                    final AbstractVariableReference referencedInThis = fieldsThis.get(entry.getKey());
                    if (referencedInThis == null
                        || !new Pair<>(referencedInThis, entry.getValue()).equals(commonFields.get(entry.getKey())))
                    {
                        lostFieldThat = true;
                        break;
                    }
                }
            }

            /*
             * Do not create an AbstractInstance here!
             *
             * In the resulting TRS a field value read from an abstract instance
             * has no visible connection to the parent object. A list traversal
             * while (c != null) { c = c.next; } cannot be shown terminating
             * with c as an AbstractInstance (and not using Path Length).
             *
             * Also, for the following code snippet the variant with an
             * AbstractInstance for this cannot store that the field is not null
             * when retrieving it for the second time. This, however, is needed
             * to show termination of MainFind.jar (and others).
             *
             * if (this.next != null) {
             *      this.next.foo();
             * }
             *
             * With ObjectInstance: no NPE
             * With AbstractInstance: NPE
             */
            ObjectInstance instance;
            if (varThis instanceof AbstractInstance && varThat instanceof AbstractInstance) {
                instance = new AbstractInstance();
                mergedState.addAbstractVariable(resRef, instance);
            } else {
                ClassName retainForClassName = JAVA_LANG_OBJECT.getClassName();
                for (final FieldIdentifier fieldIdentifier : commonFields.keySet()) {
                    final ClassName className = fieldIdentifier.getClassName();
                    final TypeTree typeTree = cPath.getTypeTree(className);
                    if (typeTree.isProperSubClassOf(retainForClassName)) {
                        retainForClassName = className;
                    }
                }

                instance =
                    ConcreteInstance.newInstanceFromType(
                        mergedState,
                        cPath.getTypeTree(retainForClassName),
                        FieldValueSettings.NULL_VALUE);

                for (final Entry<FieldIdentifier, Pair<AbstractVariableReference, AbstractVariableReference>> entry : commonFields
                    .entrySet())
                {
                    final FieldIdentifier fieldIdentifier = entry.getKey();
                    ConcreteInstance currentSlice = ((ConcreteInstance) instance).getMostSpecializedInstance();
                    while (currentSlice != null) {
                        if (currentSlice.getType().getClassName().equals(fieldIdentifier.getClassName())) {
                            final AbstractVariableReference ref = newResult.getVarCache().get(entry.getValue());
                            currentSlice.setField(fieldIdentifier.getFieldName(), ref);
                        }
                        currentSlice = currentSlice.getSuperClassInstance();
                    }
                }
                mergedState.removeAbstractVariable(resRef);
                mergedState.addAbstractVariable(resRef, instance);

                /*
                 * We must add costs if the result does not represent a field anymore. However, we must not add costs if no
                 * information was lost at all!
                 */
                if (varThis instanceof ConcreteInstance) {
                    final ConcreteInstance varInstanceThis = (ConcreteInstance) varThis;
                    if (!varInstanceThis.isOnlyRealizedUpToJLO()) {
                        if (!thisVarRef.equals(newResult.getReplacementReference()) && lostFieldThis) {
                            newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
                        }
                    }
                } else if (varThis instanceof Array) {
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thisVarRef, thatVarRef, false);
                }
                if (varThat instanceof ConcreteInstance) {
                    final ConcreteInstance varInstanceThat = (ConcreteInstance) varThat;
                    if (!varInstanceThat.isOnlyRealizedUpToJLO()) {
                        if (!thatVarRef.equals(newResult.getReplacementReference()) && lostFieldThat) {
                            newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
                        }
                    }
                } else if (varThat instanceof Array) {
                    newResult.addCost(CostType.LOST_REALIZED_INFO, thatVarRef, thisVarRef, true);
                }
            }
        }
    }

    private static Set<JBCIntegerRelation> findIntegerRelations(State state, HeapPositions heapPos) {
        ClassPath cPath = state.getClassPath();
        //the explicit relations
        Set<JBCIntegerRelation> res = new LinkedHashSet<>(state.getIntegerRelations().getRelations());

        //the implicit relations
        //get all refs
        List<AbstractVariableReference> references = new LinkedList<>(heapPos.getReferencesAndPositions().keySet());
        for (Iterator<AbstractVariableReference> it = references.iterator(); it.hasNext();) {
            AbstractVariableReference ref = it.next();
            //remove all refs not pointing to int
            if (!ref.pointsToAnyIntegerType()) {
                it.remove();
                continue;
            }
            //remove all refs in final static fields
            for (StatePosition pos : heapPos.getPositionsForRef(ref)) {
                if (pos instanceof StaticFieldRootPosition) {
                    StaticFieldRootPosition rootPos = (StaticFieldRootPosition) pos;
                    Field field = cPath.getClass(rootPos.getClassName()).getStaticFields().get(rootPos.getFieldName());
                    if (field.isFinal()) {
                        it.remove();
                        break;
                    }
                }
            }
        }

        references = new ArrayList<>(references);
        //compare them pairwise
        for (int i=0; i<references.size(); i++) {
            AbstractVariableReference refA = references.get(i);
            AbstractInt intA = (AbstractInt)state.getAbstractVariable(refA);
            for (int j=i+1; j<references.size(); j++) {
                AbstractVariableReference refB = references.get(j);
                AbstractInt intB = (AbstractInt)state.getAbstractVariable(refB);

                //check the relation of intA and intB
                IntegerRelationType relationType= AbstractInt.computeRelationType(intA, intB);
                if (relationType != null) {
                    res.add(new JBCIntegerRelation(refA, relationType, refB));
                }
            }
        }
        return res;
    }

    private static void mergeIntegerRelations(
        final State sourceState,
        final State checkInState,
        final JBCMergeResult newResult) throws TooExpensiveException
    {
        boolean isOther = sourceState == newResult.getPartnerState();
        final State resultState = newResult.getMergedState();
        //TODO: These should be cached, but the merge result only has heap pos without primitives (why?)
        final HeapPositions sourceHeapPos = new HeapPositions(sourceState, true);
        final HeapPositions checkInHeapPos = new HeapPositions(checkInState, true);
        final HeapPositions resultHeapPos = new HeapPositions(resultState, true);
        Deque<JBCIntegerRelation> todo = new ArrayDeque<>(findIntegerRelations(sourceState, sourceHeapPos));
        nextRel: while (!todo.isEmpty()) {
            JBCIntegerRelation sourceRel = todo.removeFirst();
            //Construct all analogous relations in the other state by finding merge partners using state positions:
            final AbstractVariableReference leftSourceRef = sourceRel.getLeftIntRef();
            final AbstractVariableReference rightSourceRef = sourceRel.getRightIntRef();
            final IntegerRelationType relType = sourceRel.getRelationType();

            if (!sourceHeapPos.containsRef(leftSourceRef) || !sourceHeapPos.containsRef(rightSourceRef)) {
                continue;
            }
            for (final StatePosition leftSourceRefPos : sourceHeapPos.getPositionsForRef(leftSourceRef)) {
                //The reference needs to be available at all positions:
                if (!checkInHeapPos.hasPosition(leftSourceRefPos)) {
                    continue nextRel;
                }
                final AbstractVariableReference leftCheckRef = checkInHeapPos.getReferenceForPos(leftSourceRefPos);
                for (final StatePosition rightSourceRefPos : sourceHeapPos.getPositionsForRef(rightSourceRef)) {
                    //The reference needs to be available at all positions:
                    if (!checkInHeapPos.hasPosition(rightSourceRefPos)) {
                        continue nextRel;
                    }
                    final AbstractVariableReference rightCheckRef =
                        checkInHeapPos.getReferenceForPos(rightSourceRefPos);

                    //Construct the analogous relation:
                    final JBCIntegerRelation relToCheck = new JBCIntegerRelation(leftCheckRef, relType, rightCheckRef);

                    if (!checkInState.checkIntegerRelation(relToCheck)) {
                        Collection<AbstractVariableReference> sourceRefs = Arrays.asList(new AbstractVariableReference[]{leftSourceRef, rightSourceRef});
                        Collection<AbstractVariableReference> checkRefs = Arrays.asList(new AbstractVariableReference[]{leftCheckRef, rightCheckRef});
                        newResult.addCost(CostType.LOST_INT_REL, sourceRefs, checkRefs, 1.0, isOther);
                        //We failed, try weaker relations and continue
                        for (IntegerRelationType r : sourceRel.getRelationType().getWeakerRelationTypes()) {
                            if (r != IntegerRelationType.NE)
                                todo.addFirst(new JBCIntegerRelation(leftSourceRef, r, rightSourceRef));
                        }
                        continue nextRel;
                    }

                    final AbstractVariableReference leftResultRef =
                        resultHeapPos.getReferenceForPos(leftSourceRefPos, true);
                    final AbstractVariableReference rightResultRef =
                        resultHeapPos.getReferenceForPos(rightSourceRefPos, true);

                    if (leftResultRef != null && rightResultRef != null) {
                        resultState.getIntegerRelations().note(leftResultRef, relType, rightResultRef);
                    }
                }
            }
        }
    }

    /**
     * In case of a refine reversible check for an equality refinement, we need
     * to first merge the replacement reference (with possibly more information)
     * so that we indeed have an instance.
     * @param beforeRefine the state before refinement
     * @param afterRefine the state after refinement
     * @param newResult the result to be constructed
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void refineReversibleVoodoo(
        final State afterRefine,
        final State beforeRefine,
        final JBCMergeResult newResult) throws TooExpensiveException
    {
        final AbstractVariableReference ref = newResult.getReplacementReference();
        if (ref == null) {
            return;
        }

        // first check if we indeed removed a possible equality for ref
        boolean foundOne = false;
        for (final AbstractVariableReference partner : beforeRefine
            .getHeapAnnotations()
            .getEqualityGraph()
            .getPartners(ref))
        {
            if (!afterRefine.getHeapAnnotations().getEqualityGraph().areMarkedAsPossiblyEqual(ref, partner)) {
                foundOne = true;
            }
        }
        assert (foundOne);

        /*
         * Now we need a position that contains ref in both states. Since
         * afterRefine does not contain the other reference at all, we can
         * take any position of ref in beforeRefine.
         */
        newResult.createHeapPositions(null, beforeRefine, null);
        final HeapPositions heapPos = newResult.getHeapPositionsB();
        final StatePosition pos = heapPos.getShortestPositionForRef(ref);
        PathMerger.mergeVariableReferences(afterRefine, beforeRefine, newResult, pos);
    }

    /**
     * @param thisState one of the two involved states
     * @param thatState the other state
     * @param newResult the result being constructed
     * @param frameNum the position of the stack frames to be merged
     * @throws TooExpensiveException if merging is aborted.
     */
    private static void mergeInputReferences(
        final State thisState,
        final State thatState,
        final JBCMergeResult newResult,
        final int frameNum) throws TooExpensiveException
    {
        final State mergedState = newResult.getMergedState();
        final VariableCache varCache = newResult.getVarCache();
        final InputReferences thisReferences = thisState.getCallStack().get(frameNum).getInputReferences();
        final InputReferences thatReferences = thatState.getCallStack().get(frameNum).getInputReferences();
        final InputReferences mergedReferences = mergedState.getCallStack().get(frameNum).getInputReferences();

        /*
         * We only want to merge if both states have the same set of root
         * positions, which is only really interesting for input references.
         */
        if (Globals.useAssertions) {
            final Collection<InputRefRootPosition> thisPos = thisReferences.getIRPositions(frameNum);
            final Collection<InputRefRootPosition> thatPos = thatReferences.getIRPositions(frameNum);
            assert (thisPos.equals(thatPos));
        }

        Map<FieldIdentifier, IRChangeInformations> thisSFs = thisReferences.getChangedSF();
        Map<FieldIdentifier, IRChangeInformations> thatSFs = thatReferences.getChangedSF();
        Map<FieldIdentifier, IRChangeInformations> mergedSFs = mergedReferences.getChangedSF();
        Set<FieldIdentifier> changedSFs = new HashSet<>(thisSFs.keySet());
        changedSFs.addAll(thatSFs.keySet());
        IRChangeInformations defaultV = new IRChangeInformations();
        for (FieldIdentifier changedField : changedSFs) {
            IRChangeInformations mergedChange = thisSFs.getOrDefault(changedField, defaultV).copy();
            IRChangeInformations thatChange = thatSFs.getOrDefault(changedField, defaultV);

            if (!thatChange.containsChanges(mergedChange, varCache::contains)) {
                newResult.addCost(
                        CostType.MODIFIED_INPUTREF,
                        Collections.<AbstractVariableReference>emptySet(),
                        Collections.<AbstractVariableReference>emptySet(),
                        1,
                        true);
            }
            if (mergedChange.merge(thatChange, varCache)) {
                newResult.addCost(
                        CostType.MODIFIED_INPUTREF,
                        Collections.<AbstractVariableReference>emptySet(),
                        Collections.<AbstractVariableReference>emptySet(),
                        1,
                        false);
            }
            mergedSFs.put(changedField, mergedChange);
        }

        for (final InputReference irThis : thisReferences) {
            final InputReference irThat = thatReferences.getInputReference(irThis);
            assert (irThat != null);

            final StatePosition pos = irThis.getIRStatePosition(frameNum);
            final AbstractVariableReference mergedRef = PathMerger.mergeVariableReferences(thisState, thatState, newResult, pos);
            final InputReference irResult = irThis.clone();
            irResult.replaceReference(mergedRef);

            if (!irThat.containsChanges(irThis.getChanges(), varCache::contains)) {
                irThat.containsChanges(irThis.getChanges(), varCache::contains);
                newResult.addCost(
                        CostType.MODIFIED_INPUTREF,
                        Collections.emptySet(),
                        Collections.emptySet(),
                        1,
                        true);
            }

            if (irResult.mergeChanges(irThat.getChanges(), varCache)) {
                newResult.addCost(
                        CostType.MODIFIED_INPUTREF,
                        Collections.emptySet(),
                        Collections.emptySet(),
                        1,
                        false);
            }
            mergedReferences.add(irResult);
        }
    }
}
