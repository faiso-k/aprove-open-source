package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * For an end state in some method graph, this class is used to connect states representing calls to that method to
 * states representing the finished call (i.e., all return values and side-effects of the called method are regarded).
 * @author cotto
 */
public final class MethodEndHelper {
    /**
     * Do not instantiate me.
     */
    private MethodEndHelper() {

    }

    /**
     * The state endingState in the method graph endingGraph is needs to be regarded as another method end, meaning the
     * callingNode in callingGraph gets a new successor.
     * @param endingGraph the graph containing endingState
     * @param endingState a state with a new method end
     * @param callingGraph the graph containing callingNode
     * @param callingNode a node calling the method of endingGraph
     * @return tasks for a) a failed intersection b) a new state representing the successor of the method call c) null
     * if nothing needs to be done (e.g. because failed intersections are not added) d) a new end state, which is an
     * abstracted version from the one given as an argument (to deal with =?= issues for realized instances)
     */
    public static Collection<MethodGraphWorker> newMethodEnd(
        final MethodGraph endingGraph,
        final State endingState,
        final MethodGraph callingGraph,
        final Node callingNode)
    {
        // There should be exactly one stack frame in the new method end
        if (Globals.useAssertions) {
            assert (endingState.getCallStack().size() == 1);
        }
        // The calling state in this graph
        final State callingState = callingNode.getState();

        Node current = callingNode;
        State abstractedCallingState = null;
        WHILE: while (true) {
            for (final Edge edge : current.getOutEdges()) {
                if (edge.getLabel() instanceof CallAbstractEdge || edge.getLabel() instanceof InstanceEdgeTryToConnect)
                {
                    current = edge.getEnd();
                    continue WHILE;
                }
            }
            abstractedCallingState = current.getState();
            break;
        }
        assert (abstractedCallingState != null);

        /*
         * Get the modified ending state where we only consider the input references that correspond to the call state.
         * Furthermore, all references are fresh.
         */
        final Pair<State, BidirectionalMap<AbstractVariableReference, AbstractVariableReference>> pair =
            MethodEndHelper.getCleanedRenamedEndingState(endingState, callingState);
        final State newEndingState = pair.x;
        final State renamedEndingState = newEndingState.clone();
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> endingToRenamedEnding = pair.y;

        /*
         * Identify the references that were visible in the both the invoked method and the invoking method.
         */
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnUnchanged =
            new BidirectionalMap<>();
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnChanged =
            new BidirectionalMap<>();

        MethodEndHelper.getReferenceCorrespondence(
            callToReturnChanged,
            callToReturnUnchanged,
            callingState,
            newEndingState,
            abstractedCallingState);

        /*
         * For the intersection we construct a modified variant of callingState where the opcode is advanced to return
         * and new information from the returning state is added (initialized classes, static fields, objects that were
         * created after the invocation).
         */
        final State callWithEndData =
            MethodEndHelper.getCallWithEndData(callingState, newEndingState, callToReturnChanged, callToReturnUnchanged);

        final Node endingNode = endingGraph.getNode(endingState);

        if (endingNode == null) {
            // the end state does not exist anymore, no need to return here
            return null;
        }

        callWithEndData.gc();

        // mark the changed references as changed in the calling stack frame
        HeapPositions callWithEndDataHeapPos = new HeapPositions(callWithEndData);
        for (final InputReference ir : newEndingState.getInputReferences()) {
            if (!ir.getChanged()) {
                continue;
            }
            for (final StackFrame sf : callWithEndData.getCallStack().getStackFrameList()) {
                sf.getInputReferences().addChanges(callWithEndDataHeapPos, ir.getReference(), ir.getChanges().asChangesFromLowerFrame(endingToRenamedEnding));
            }
        }
        // mark the changed static fields as changed in the calling stack frame
        for (final Entry<FieldIdentifier, IRChangeInformations> entry : newEndingState
            .getInputReferences()
            .getChangedSF()
            .entrySet())
        {
            for (final StackFrame sf : callWithEndData.getCallStack().getStackFrameList()) {
                sf.getInputReferences().getChangedSF().put(entry.getKey(), entry.getValue().asChangesFromLowerFrame(endingToRenamedEnding));
            }
        }

        /*
         * Add the lower stack frames from calling state to callWithEndData and
         * rename accordingly.
         */
        MethodEndHelper.prependStackFrames(newEndingState, callingState, callWithEndData, callToReturnUnchanged, callToReturnChanged);

        newEndingState.gc();

        final Triple<State, Map<AbstractVariableReference, AbstractVariableReference>, Map<AbstractVariableReference, AbstractVariableReference>> triple;
        try {
            if (JBCOptions.DEBUG_METHODEND) {
                System.out.println("Intersecting:");
                System.out.println(callingState);
                System.out.println(renamedEndingState);
                System.out.println(callToReturnChanged);
                System.out.println(callToReturnUnchanged);
                System.out.println(callWithEndData);
                System.out.println(newEndingState);
            }
            triple = Intersector.intersectAndRename(callWithEndData, newEndingState);
        } catch (final IntersectionFailException e) {
            if (JBCOptions.DEBUG_METHODEND) {
                System.out.println("======================");
                System.out.println(e);
                System.out.println("======================");
            }
            return Collections.<MethodGraphWorker>singleton(new StateAdder(
                    callingGraph,
                    callingNode,
                    newEndingState,
                    new FailedIntersectionEdge(e.toString(), endingNode)));
        }
        /*
         * The intersection went through, now we need to add a MethodSkipEdge with a lot of renaming information to the
         * graph.
         */
        final State intersected = triple.x;

        final Map<AbstractVariableReference, AbstractVariableReference> renamedEndingToIntersected = triple.z;

        if (JBCOptions.DEBUG_METHODEND) {
            System.out.println("======================");
            System.out.println(intersected);
            System.out.println("======================");
            /*
             * Check that 1) there is no existing reference without
             * corresponding abstract variable and 2) no abstract type is
             * missing.
             */
            for (final AbstractVariableReference ref : intersected.getReferences().keySet()) {
                if (ref.isNULLRef() || !ref.pointsToReferenceType()) {
                    continue;
                }
                assert (intersected.getAbstractVariable(ref) != null || intersected
                    .getHeapAnnotations()
                    .isMaybeExisting(ref));
                assert (intersected.getAbstractType(ref) != null);
            }
        }

        // remove the input refernces of the top stack frame
        intersected.getInputReferences().getNonRootInputReferences().clear();
        intersected.getInputReferences().getRootInputReferences().clear();

        final Set<AbstractVariableReference> knownReferences = intersected.getReferences().keySet();

        if (endingGraph.getNode(endingState) == null) {
            // the end state does not exist anymore, no need to return here
            return null;
        }

        /*
         * Based on the existing renaming maps, construct a map for the renaming from endingState to the intersected
         * state (via newEndingState)
         */
        final Map<AbstractVariableReference, AbstractVariableReference> endingToIntersected =
            MethodEndHelper.combineRenaming(knownReferences, endingToRenamedEnding, renamedEndingToIntersected);


        /*
         * A renaming from the call state to a pair containing the renamed ref in the result state and in the ending state for all changed references
         */
        final Map<AbstractVariableReference, Pair<AbstractVariableReference, AbstractVariableReference>> callToResultEndChanged =
            MethodEndHelper.combineRenaming(knownReferences, callToReturnChanged, renamedEndingToIntersected).entrySet().stream()
            .collect(Collectors.toMap(entry -> entry.getKey(),
                                      entry -> new Pair<>(entry.getValue(),
                                                          endingToRenamedEnding.getRL(callToReturnChanged.getLR(entry.getKey())))));


        /*
         * The MethodSkipEdge, which we will create later using this information, demands that the renaming only
         * contains unchanged references.
         */
        final Map<AbstractVariableReference, AbstractVariableReference> callingToResult = triple.y;
        callingToResult.keySet().removeAll(callToReturnChanged.keySetLR());

        // remove the references which do not exist anymore
        final Collection<AbstractVariableReference> remove = new LinkedHashSet<>();
        for (final Entry<AbstractVariableReference, AbstractVariableReference> entry : callingToResult.entrySet()) {
            if (!knownReferences.contains(entry.getValue())) {
                remove.add(entry.getKey());
            }
        }
        for (final AbstractVariableReference ref : remove) {
            callingToResult.remove(ref);
        }

        remove.clear();
        for (final Entry<AbstractVariableReference, AbstractVariableReference> entry : endingToIntersected.entrySet()) {
            if (!knownReferences.contains(entry.getValue())) {
                remove.add(entry.getKey());
            }
        }
        for (final AbstractVariableReference ref : remove) {
            endingToIntersected.remove(ref);
        }

        intersected.gc();

        return Collections.<MethodGraphWorker>singleton(new StateAdder(
            callingGraph,
            callingNode,
            intersected,
            new MethodSkipEdge(endingNode, endingGraph, callingToResult, callToResultEndChanged, endingToIntersected)));
    }

    /**
     * Identify the references that were visible in the both the invoked method and the invoking method.
     * @param callToReturnChanged the renaming of changed references
     * @param callToReturnUnchanged the renaming of unchanged references
     * @param callingState the state calling the invoked method
     * @param newEndingState the (renamed) ending state
     * @param abstractedCallingState the abstracted call state (with input references)
     */
    private static void getReferenceCorrespondence(
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnChanged,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnUnchanged,
        final State callingState,
        final State newEndingState,
        final State abstractedCallingState)
    {

        // get the information from the input references
        for (final InputReference inputRef : newEndingState.getInputReferences()) {
            // does this input reference exist in the calling state?
            final InputReference irCalling = abstractedCallingState.getInputReferences().getCorrespondingIR(inputRef);
            if (irCalling == null) {
                // no correspondence
                continue;
            }

            final AbstractVariableReference retRef = inputRef.getReference();
            final AbstractVariableReference callRef = inputRef.getOriginalReference(callingState);
            if (inputRef.getChanged()) {
                if (!callRef.isNULLRef() && !callRef.pointsToConstant()) {
                    callToReturnChanged.putLR(callRef, retRef);
                }
            } else if (!callRef.equals(retRef)) {
                callToReturnUnchanged.putLR(callRef, retRef);
            }
        }

        // consider the static fields
        for (final ClassName className : callingState.getStaticFields().getClasses()) {
            for (final String name : callingState.getStaticFields().getNames(className)) {
                final AbstractVariableReference refCalling = callingState.getStaticFields().get(className, name);
                final AbstractVariableReference refNewEnding = newEndingState.getStaticFields().get(className, name);
                if (!newEndingState.getInputReferences().getChangedSF().containsKey(new Pair<>(className, name))
                    && !refCalling.equals(refNewEnding))
                {
                    callToReturnUnchanged.putLR(refCalling, refNewEnding);
                }
            }
        }

        /*
         * Also identify the correspondence for references which are only reachable from some unchanged input reference.
         */
        final Map<AbstractVariableReference, AbstractVariableReference> add = new LinkedHashMap<>();
        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entry : callToReturnUnchanged
            .getEntriesLR())
        {
            final AbstractVariableReference refCalling = entry.getKey();
            final AbstractVariableReference refEnding = entry.getValue();
            if (refCalling.isNULLRef() || !refCalling.pointsToReferenceType()) {
                continue;
            }
            for (final Map.Entry<AbstractVariableReference, NonRootPosition> reachEntry : Reachability
                .getReachableRefsWithSuffix(
                    refCalling,
                    true,
                    Collections.<AbstractVariableReference>emptySet(),
                    null,
                    callingState)
                .entrySet())
            {
                final AbstractVariableReference reachRef = reachEntry.getKey();
                if (callToReturnUnchanged.containsKeyLR(reachRef)) {
                    continue;
                }
                final NonRootPosition suffix = reachEntry.getValue();
                final AbstractVariableReference reachEnding = suffix.getFromState(refEnding, newEndingState);
                if (reachEnding != null && !reachRef.equals(reachEnding)) {
                    add.put(reachRef, reachEnding);
                }
            }
        }

        callToReturnUnchanged.putAllLR(add);
    }

    /**
     * Add the lower stack frames from callWithEndData and rename the references so that the data from newEndingState is
     * used for known references.
     * @param callingState the state calling the invoked method
     * @param newEndingState the (renamed) ending state
     * @param callWithEndData the calling state with data from newEndingState
     * @param callToReturnUnchanged the renaming of unchanged references
     * @param callToReturnChanged the renaming of changed references
     */
    private static void prependStackFrames(
        final State newEndingState,
        final State callingState,
        final State callWithEndData,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnUnchanged,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnChanged)
    {
        final Collection<AbstractVariableReference> refsBefore = newEndingState.getReferences().keySet();
        newEndingState.addAllDataFrom(callingState);

        boolean first = true;
        for (final StackFrame sf : callWithEndData.getCallStack().getStackFrameList()) {
            if (first) {
                first = false;
                continue;
            }
            final StackFrame clone = sf.clone();
            newEndingState.getCallStack().getStackFrameList().add(clone);
        }

        MethodEndHelper.replaceReferences(newEndingState, callToReturnUnchanged.getLRMap());
        MethodEndHelper.replaceReferences(newEndingState, callToReturnChanged.getLRMap());

        // find the references that were not known in the returning state
        final Collection<AbstractVariableReference> newRefs = newEndingState.getReferences().keySet();
        newRefs.removeAll(refsBefore);
        final Collection<AbstractVariableReference> remove = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : newRefs) {
            if (!ref.pointsToReferenceType() || ref.isNULLRef()) {
                remove.add(ref);
            }
        }
        newRefs.removeAll(remove);

        final HeapPositions heapPosCalling = new HeapPositions(callingState);
        for (final AbstractVariableReference ref : newRefs) {
            final Collection<AbstractVariableReference> preds = heapPosCalling.getAllPredecessors(ref, false);
            preds.addAll(callingState.getHeapAnnotations().getJoiningStructures().getReferencesWithPartner(ref));
            for (final AbstractVariableReference pred : preds) {
                if (callToReturnUnchanged.containsKeyLR(pred)) {
                    final AbstractVariableReference inReturn = callToReturnUnchanged.getLR(pred);
                    final AbstractVariable var = newEndingState.getAbstractVariable(inReturn);
                    if (var instanceof ConcreteInstance) {
                        if (var.isNULL() || !((ConcreteInstance) var).isOnlyRealizedUpToJLO()) {
                            continue;
                        }
                    }
                    newEndingState.getHeapAnnotations().getJoiningStructures().add(inReturn, ref);
                }

                /*
                 * Even if we knew for sure that the reference was changed, we have no idea what was changed. So it
                 * might be that the link to ref is still there. Besides, adding a joins is always correct here.
                 */
                if (callToReturnChanged.containsKeyLR(pred)) {
                    final AbstractVariableReference inReturn = callToReturnChanged.getLR(pred);
                    final AbstractVariable var = newEndingState.getAbstractVariable(inReturn);
                    if (var instanceof ConcreteInstance) {
                        if (!((ConcreteInstance) var).isOnlyRealizedUpToJLO()) {
                            continue;
                        }
                    }
                    newEndingState.getHeapAnnotations().getJoiningStructures().add(inReturn, ref);
                }

            }
        }
    }

    /**
     * @param callingState the state calling the invoked method
     * @param newEndingState the (renamed) ending state
     * @param callToReturnUnchanged the renaming of unchanged references
     * @param callToReturnChanged the renaming of changed references
     * @return the calling state with data from the ending state. Note that the references are from the renamed ending state.
     */
    private static State getCallWithEndData(
        final State callingState,
        final State newEndingState,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnChanged,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnUnchanged)
    {
        final State callWithEndData = callingState.clone();

        // Advance the opcode of the modified calling state to "return"
        MethodEndHelper.advanceToReturnOpcode(callWithEndData, newEndingState, callToReturnUnchanged);

        /*
         * Find references introduced in the returning stack frame for which we do not have any corresponding (old)
         * reference.
         */
        final Map<AbstractVariableReference, Integer> res = new DefaultValueMap<>(0);
        callWithEndData.getCallStack().getTop().getReferences(res);

        final Collection<AbstractVariableReference> newRefs = new LinkedHashSet<>(res.keySet());

        // also add the reachable references!

        /*
         * Add all data from the renamed ending state (which has disjoint references).
         */
        callWithEndData.addAllDataFrom(newEndingState);

        final Collection<AbstractVariableReference> addMe = new LinkedHashSet<>();
        for (final AbstractVariableReference newRef : newRefs) {
            if (newRef.isNULLRef() || !newRef.pointsToReferenceType()) {
                continue;
            }
            addMe.addAll(Reachability.getReachableRefs(newRef, false, callWithEndData));
        }
        newRefs.addAll(addMe);

        newRefs.removeAll(callingState.getReferences().keySet());
        newRefs.removeAll(callToReturnUnchanged.keySetRL());

        // throw out primitives and null
        newRefs.remove(AbstractVariableReference.NULLREF);
        final Iterator<AbstractVariableReference> it = newRefs.iterator();
        while (it.hasNext()) {
            final AbstractVariableReference next = it.next();
            if (!next.pointsToReferenceType()) {
                it.remove();
            }
        }

        // use the reference names from the call (where applicable)
        MethodEndHelper.replaceReferences(callWithEndData, callToReturnUnchanged.getRLMap());

        /*
         * For the new references also add the renamed sharing information from the annotations.
         */
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> addEquality =
            new LinkedHashSet<>();
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> addJoins = new LinkedHashSet<>();
        for (final AbstractVariableReference ref : newRefs) {
            for (final AbstractVariableReference partner : callWithEndData
                .getHeapAnnotations()
                .getEqualityGraph()
                .getPartners(ref))
            {
                if (callToReturnUnchanged.containsKeyRL(partner)) {
                    final AbstractVariableReference newPartner = callToReturnUnchanged.getRL(partner);
                    addEquality.add(new Pair<>(ref, newPartner));
                }
            }
            for (final AbstractVariableReference partner : callWithEndData
                .getHeapAnnotations()
                .getJoiningStructures()
                .getReferencesWithPartner(ref))
            {
                if (callToReturnUnchanged.containsKeyRL(partner)) {
                    final AbstractVariableReference newPartner = callToReturnUnchanged.getRL(partner);
                    addJoins.add(new Pair<>(ref, newPartner));
                }
            }
        }

        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : addEquality) {
            final AbstractVariableReference ref = pair.x;
            final AbstractVariableReference newPartner = pair.y;
            callWithEndData
                .getHeapAnnotations()
                .getEqualityGraph()
                .addPossibleEquality(callWithEndData, ref, newPartner);
        }
        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : addJoins) {
            final AbstractVariableReference ref = pair.x;
            final AbstractVariableReference newPartner = pair.y;
            callWithEndData.getHeapAnnotations().getJoiningStructures().add(ref, newPartner);
        }

        // for the parts that are changed or new, use data from newEndingState
        MethodEndHelper.replaceChangedAndNewReferences(newEndingState, callWithEndData, callToReturnChanged);

        /*
         * For new references that were refined but not changed, we may now have visible child references. Allow this
         * connection in the modified call state by adding joins annotations.
         */
        final HeapPositions heapPosEnding = new HeapPositions(newEndingState);
        for (final AbstractVariableReference ref : newRefs) {
            final Collection<AbstractVariableReference> preds = heapPosEnding.getAllPredecessors(ref, false);
            preds.addAll(callingState.getHeapAnnotations().getJoiningStructures().getReferencesWithPartner(ref));
            for (final AbstractVariableReference pred : preds) {
                if (callToReturnUnchanged.containsKeyRL(pred)) {
                    final AbstractVariableReference inCall = callToReturnUnchanged.getRL(pred);
                    callWithEndData.getHeapAnnotations().getJoiningStructures().add(inCall, ref);
                }
            }
        }

        return callWithEndData;
    }

    /**
     * Advances the opcode to the return opcode (of newEndingState).
     * @param callWithEndData the calling state with data from newEndingState
     * @param newEndingState the (renamed) ending state
     * @param callToReturnUnchanged the renaming of unchanged references
     */
    private static void advanceToReturnOpcode(
        final State callWithEndData,
        final State newEndingState,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnUnchanged)
    {

        callWithEndData.getCallStack().pop();
        final StackFrame endFrame = newEndingState.getCallStack().getTop();
        final StackFrame endFrameClone = endFrame.clone();
        callWithEndData.getCallStack().push(endFrameClone);
    }

    /**
     * @param knownReferences the references in the (modified) intersected state
     * @param renamedEndingToIntersected a renaming map
     * @param endingToRenamedEnding a renaming map
     * @return a renaming map from the ending state to the intersected state (via renamedEndingState)
     */
    private static Map<AbstractVariableReference, AbstractVariableReference> combineRenaming(
        final Set<AbstractVariableReference> knownReferences,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> endingToRenamedEnding,
        final Map<AbstractVariableReference, AbstractVariableReference> renamedEndingToIntersected)
    {
        final Map<AbstractVariableReference, AbstractVariableReference> endingToIntersected = new LinkedHashMap<>();

        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entry : endingToRenamedEnding
            .getEntriesLR())
        {
            final AbstractVariableReference newName =
                MethodEndHelper.getIntersectedRefForNewEndingRef(entry.getValue(), knownReferences, renamedEndingToIntersected);
            if (newName == null) {
                continue;
            }
            endingToIntersected.put(entry.getKey(), newName);
        }
        return endingToIntersected;
    }

    /**
     * @param ref a reference
     * @param knownReferences the references in the (modified) intersected state
     * @param renamedEndingToIntersected a renaming map
     * @return the reference in intersected that corresponds to ref in renamedEndingState, null if no such reference
     * exists.
     */
    private static AbstractVariableReference getIntersectedRefForNewEndingRef(
        final AbstractVariableReference ref,
        final Collection<AbstractVariableReference> knownReferences,
        final Map<AbstractVariableReference, AbstractVariableReference> renamedEndingToIntersected)
    {
        AbstractVariableReference newName = renamedEndingToIntersected.get(ref);
        if (newName == null) {
            /*
             * It can be that this reference was not renamed at all, because there is no counterpart for the
             * intersection (i.e. newly created elements returned by the method or because of more detailed information
             * in the ending state than in the calling state).
             */
            if (knownReferences.contains(ref)) {
                newName = ref;
            } else {
                // this reference does not exist anymore, ignore it
                return null;
            }
        }
        return newName;
    }

    /**
     * Update callWithEndData so that new data from newEndingState is used properly (update initialized classes
     * information, set new static fields and add references with corresponding annotations for objects created after
     * the invocation).
     * @param newEndingState the (renamed) ending state
     * @param callWithEndData the state where we add the informaton from the ending state
     * @param callToReturnChanged the renaming of changed references
     */
    private static void replaceChangedAndNewReferences(
        final State newEndingState,
        final State callWithEndData,
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> callToReturnChanged)
    {
        JBCOptions options = newEndingState.getJBCOptions();
        // use class initialization information from newEndingState
        for (final Entry<ClassName, InitStatus> entry : newEndingState
            .getClassInitInfo()
            .getClassesWithInitializationState(options)
            .entrySet())
        {
            final ClassName className = entry.getKey();
            final InitStatus newStatus = entry.getValue();
            final InitStatus callStatus = callWithEndData.getClassInitInfo().getInitializationState(className, options);
            if (callStatus.equals(newStatus)) {
                continue;
            }
            assert (newStatus.equals(InitStatus.YES) || newStatus.equals(InitStatus.RUNNING));
            assert (callStatus.equals(InitStatus.MAYBE));

            callWithEndData.getClassInitInfo().setInitialized(className, newStatus);
        }

        /*
         * In case of static fields that did not exist before the call, use the new references in callWithEndData.
         */
        MethodEndHelper.setNewStaticFields(newEndingState, callWithEndData);

        /*
         * For static fields that were changed, also use the data from newEndingState.
         */
        MethodEndHelper.setChangedStaticFields(newEndingState, callWithEndData);

        /*
         * Modify the calling state so that it uses all the changed values from the returning state.
         */
        MethodEndHelper.replaceReferences(callWithEndData, callToReturnChanged.getLRMap());

        // for changed references use the type, array length and existence information from before the change
        for (final Entry<AbstractVariableReference, AbstractVariableReference> entry : callToReturnChanged
            .getEntriesLR())
        {
            final AbstractVariableReference refCall = entry.getKey();
            final AbstractVariableReference refEnd = entry.getValue();

            if (!refCall.pointsToReferenceType()) {
                continue;
            }

            final AbstractType at = callWithEndData.getAbstractType(refCall);
            callWithEndData.setAbstractType(refEnd, at);

            final AbstractVariable varCall = callWithEndData.getAbstractVariable(refCall);
            if (varCall instanceof Array) {
                final AbstractVariable varEnd = callWithEndData.getAbstractVariable(refEnd);
                if (varEnd instanceof Array) {
                    final Array arrayEnd = (Array) varEnd;
                    arrayEnd.setLength(arrayEnd.getLength());
                }
            }

            if (!callWithEndData.getHeapAnnotations().isMaybeExisting(refCall)
                && callWithEndData.getHeapAnnotations().isMaybeExisting(refEnd))
            {
                callWithEndData.getHeapAnnotations().setExistenceIsKnown(refEnd);
                final ObjectInstance oI = ConcreteInstance.newJLO(callWithEndData);
                callWithEndData.addAbstractVariable(refEnd, oI);
            }
        }
    }

    /**
     * For static fields that were changed based on the InputReference information of newEndingState, update
     * callWithEndData accordingly. This is only done for those static fields that were already known in callingState
     * (i.e., the classes were initialized already).
     * @param newEndingState the (renamed) ending state
     * @param callWithEndData the state where we add the informaton from the ending state
     */
    private static void setChangedStaticFields(final State newEndingState, final State callWithEndData) {
        for (final FieldIdentifier field : newEndingState
            .getInputReferences()
            .getChangedSF()
            .keySet())
        {
            final ClassName className = field.getClassName();
            final String name = field.getFieldName();
            assert (callWithEndData.getStaticFields().getClasses().contains(className));
            callWithEndData.getStaticFields().set(
                className,
                name,
                newEndingState.getStaticFields().get(className, name));
        }
    }

    /**
     * For every static field that does not exist in callWithEndData, set the value based on the information in
     * newEndingState.
     * @param newEndingState the (renamed) ending state
     * @param callWithEndData the calling state with data from newEndingState
     */
    private static void setNewStaticFields(final State newEndingState, final State callWithEndData) {
        for (final ClassName className : newEndingState.getStaticFields().getClasses()) {
            if (callWithEndData.getStaticFields().getClasses().contains(className)) {
                // not a new field
                continue;
            }
            for (final String name : newEndingState.getStaticFields().getNames(className)) {
                final AbstractVariableReference ref = newEndingState.getStaticFields().get(className, name);
                callWithEndData.getStaticFields().set(className, name, ref);
            }
        }
    }

    /**
     * Replace the references according to the given map, but do not replace the null reference.
     * @param state the state to replace in
     * @param map the map giving details about the replacement
     */
    private static void replaceReferences(
        final State state,
        final Map<AbstractVariableReference, AbstractVariableReference> map)
    {
        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> entry : map.entrySet()) {
            final AbstractVariableReference from = entry.getKey();

            if (from.isNULLRef()) {
                continue;
            }

            final AbstractVariableReference to = entry.getValue();
            state.replaceReferencesWithoutAnnotations(from, to);
        }
    }

    /**
     * Rename all references in the state and remove unnecessary input references.
     * @param endingState the state returning from the invoked method
     * @param callingState the state calling the invoked method
     * @return the modified ending state where we only consider the input references that correspond to the call state
     * and the applied substitution.
     */
    private static
        Pair<State, BidirectionalMap<AbstractVariableReference, AbstractVariableReference>>
        getCleanedRenamedEndingState(final State endingState, final State callingState)
    {
        final State result = endingState.clone();

        // remove the input references that are only used for other calls
        MethodEndHelper.removeOtherInputReferences(result, callingState);

        // rename all references
        final BidirectionalMap<AbstractVariableReference, AbstractVariableReference> map =
            result.replaceAllReferences();

        /*
         * If we have a NRIR for the calling state, we cannot use it directly. Instead, we split the NRIR into two
         * parts. The first part represents the reference that is contained in the "standard" part of the calling state,
         * the other part represents the NRIR (for the other stack frames, from previous calls in a recursive call
         * pattern).
         */
        MethodEndHelper.splitNRIRs(result, callingState);

        result.gc();

        return new Pair<>(result, map);
    }

    /**
     * For a NRIR x corresponding to exactly two references y, z in callingState, we create two new NRIRs. If y is a
     * standard reference and z is a NRIR, one of the two created NRIRs represents everything x represented except y.
     * The other NRIR just represents y. This method takes care to also add the necessary annotations.
     * @param result the state where all NRIRs are split
     * @param callingState the state calling the invoked method
     */
    private static void splitNRIRs(final State result, final State callingState) {
        final Collection<AbstractVariableReference> nrirsInCallingState = callingState.getAllNRIRs();
        final Collection<NonRootInputReference> allNRIRs =
            new LinkedHashSet<>(result.getInputReferences().getNonRootInputReferences());
        for (final NonRootInputReference nrir : allNRIRs) {
            final Collection<AbstractVariableReference> origRefs = nrir.getOriginalReferences(callingState);
            if (origRefs.size() <= 1) {
                continue;
            }
            assert (origRefs.size() == 2);

            AbstractVariableReference standardRef = null;
            AbstractVariableReference nrirRef = null;
            for (final AbstractVariableReference origRef : origRefs) {
                if (nrirsInCallingState.contains(origRef)) {
                    nrirRef = origRef;
                } else {
                    standardRef = origRef;
                }
            }
            assert (nrirRef != null);
            assert (standardRef != null);

            /*
             * We now have a NRIR in the result state for which we know both a corresponding NRIR in the calling state
             * and also some "standard" reference in that state.
             */

            final Pair<NonRootInputReference, NonRootInputReference> newNRIRs =
                nrir.split(callingState, nrirRef, standardRef);
            final NonRootInputReference newNRIR = newNRIRs.x;
            final NonRootInputReference newNRIRForStandardRef = newNRIRs.y;

            final boolean removed = result.getInputReferences().removeNRIR(nrir);
            assert (removed);
            result.getInputReferences().add(newNRIR);

            result.getInputReferences().add(newNRIRForStandardRef);

            final AbstractVariable av = result.getAbstractVariable(nrir.getReference());
            if (av != null) {
                assert (av instanceof AbstractInstance);
                result.addAbstractVariable(newNRIRForStandardRef.getReference(), av.clone());
            } else {
                assert (result.getHeapAnnotations().isMaybeExisting(nrir.getReference()));
            }
            result.getHeapAnnotations().mergeAnnotationsForNRIRMerge(
                result,
                nrir.getReference(),
                newNRIRForStandardRef.getReference());
            if (result.getHeapAnnotations().isMaybeExisting(newNRIRForStandardRef.getReference())) {
                result.removeAbstractVariable(newNRIRForStandardRef.getReference());
            }
            result
                .getHeapAnnotations()
                .getEqualityGraph()
                .addPossibleEquality(result, nrir.getReference(), newNRIRForStandardRef.getReference());

            // joins needed?
            result
                .getHeapAnnotations()
                .getJoiningStructures()
                .add(nrir.getReference(), newNRIRForStandardRef.getReference());
        }
    }

    /**
     * Remove the (non-root) input references that are irrelevant for the call from callingState.
     * @param endingState a state with a new method end
     * @param callingState a state calling the method ending in endingState
     */
    private static void removeOtherInputReferences(final State endingState, final State callingState) {
        final Collection<NonRootInputReference> remove = new LinkedHashSet<>();
        for (final NonRootInputReference nrir : endingState.getInputReferences().getNonRootInputReferences()) {
            if (!nrir.forState(callingState)) {
                remove.add(nrir);
            }
        }
        for (final NonRootInputReference removeMe : remove) {
            endingState.getInputReferences().removeNRIR(removeMe);
        }
        if (!remove.isEmpty()) {
            endingState.gc();
        }
    }
}
