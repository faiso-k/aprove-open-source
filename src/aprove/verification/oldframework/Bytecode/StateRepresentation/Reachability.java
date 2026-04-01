package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class can be used to answer questions like "what references are reachable from x"?
 */
public final class Reachability {
    /**
     * Do not instantiate me.
     */
    private Reachability() {

    }

    /**
     * Start at the given reference and follow any field from the given set until we cannot continue, run into a cycle
     * or reach the reference we want to reach.
     * @param refFrom the reference to start from
     * @param fields the fields we follow
     * @param refTo the reference we want to reach
     * @param atLeastOneStep indicates if we want to go at least one step
     * @param state the state in which we want to look
     * @return null if we run into a cycle or else the reference we reached
     */
    public static AbstractVariableReference followFields(
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fields,
        final AbstractVariableReference refTo,
        final boolean atLeastOneStep,
        final State state)
    {
        return Reachability.followFields(
            refFrom,
            fields,
            new LinkedHashSet<AbstractVariableReference>(),
            refTo,
            atLeastOneStep,
            state);
    }

    /**
     * Start at the given reference and follow any field from the given set until we cannot continue, run into a cycle
     * or reach the reference we want to reach.
     * @param refFrom the reference to start from
     * @param fields the fields we follow
     * @param seenRefs the references we already have seen, used to detect cycles
     * @param refTo the reference we want to reach
     * @param atLeastOneStep indicates if we want to go at least one step
     * @param state the state in which we want to look
     * @return The reached reference or null, if we run into a cycle or cannot go far enough.
     */
    public static AbstractVariableReference followFields(
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fields,
        final Collection<AbstractVariableReference> seenRefs,
        final AbstractVariableReference refTo,
        final boolean atLeastOneStep,
        final State state)
    {

        if (!atLeastOneStep && refFrom.equals(refTo)) {
            return refTo;
        }

        if (!seenRefs.add(refFrom)) {
            // cycle detected
            return null;
        }

        final AbstractVariable var = state.getAbstractVariable(refFrom);
        if (!(var instanceof ConcreteInstance)) {
            return (atLeastOneStep ? null : refFrom);
        }
        for (final Entry<FieldIdentifier, AbstractVariableReference> entry : ((ConcreteInstance) var)
            .getAllFields()
            .entrySet())
        {
            if (fields.contains(new InstanceFieldEdge(entry.getKey())) && !entry.getValue().isNULLRef()) {
                return Reachability.followFields(entry.getValue(), fields, seenRefs, refTo, false, state);
            }
        }
        return (atLeastOneStep ? null : refFrom);
    }

    /**
     * Start at the given reference and follow any field from the given set until we cannot continue or run into a
     * cycle.
     * @param refFrom the reference to start from
     * @param fields the fields we follow
     * @param state the state in which we want to look
     * @return all references on the path. sourceRef is always included.
     */
    public static Collection<AbstractVariableReference> followFields(
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fields,
        final State state)
    {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        Reachability.followFields(refFrom, fields, result, null, false, state);
        return result;
    }

    /**
     * Attention:
     * <ul>
     * <li>ref is not returned if it does not reach itself</li>
     * </ul>
     * @param ref a reference which must not point to a primitive value
     * @param primitives references to primitive values are returned iff this is set
     * @param state the state in which we want to look
     * @return all references reachable from ref in state, does not contain null references.
     */
    public static Collection<AbstractVariableReference> getReachableRefs(
        final AbstractVariableReference ref,
        final boolean primitives,
        final State state)
    {
        if (ref.isNULLRef()) {
            return Collections.emptySet();
        } else {
            return Reachability.getReachableRefs(ref, primitives, Collections.<AbstractVariableReference>emptySet(), state);
        }

    }

    /**
     * Attention:
     * <ul>
     * <li>ref is not returned if it does not reach itself</li>
     * </ul>
     * @param ref a reference which must not point to a primitive value
     * @param primitives references to primitive values are returned iff this is set
     * @param stopHere do not go through these references
     * @param allowedEdges if non-null, only consider these heap edges when going through the heap
     * @param state the state in which we want to look
     * @return all references reachable from ref in state, does not contain null references. The value part of the map
     * contains a non root state position that can be used to reach the key reference when starting in ref.
     */
    public static Map<AbstractVariableReference, NonRootPosition> getReachableRefsWithSuffix(
        final AbstractVariableReference ref,
        final boolean primitives,
        final Collection<AbstractVariableReference> stopHere,
        final Collection<HeapEdge> allowedEdges,
        final State state)
    {
        final Map<AbstractVariableReference, NonRootPosition> result = new LinkedHashMap<>();
        final LinkedList<Pair<AbstractVariableReference, NonRootPosition>> todo = new LinkedList<>();
        assert (!(ref instanceof ReturnAddress));
        assert (!ref.isNULLRef());
        if (!primitives) {
            assert (!(state.getAbstractVariable(ref) instanceof AbstractNumber));
        }
        todo.add(new Pair<AbstractVariableReference, NonRootPosition>(ref, null));
        boolean first = true;
        while (!todo.isEmpty()) {
            final Pair<AbstractVariableReference, NonRootPosition> pair = todo.pop();
            final AbstractVariableReference reference = pair.x;
            final NonRootPosition suffix = pair.y;
            if (!first) {
                // add ref only if we actually reach it from somewhere
                if (result.containsKey(reference)) {
                    // do not run into cycles
                    continue;
                }
                result.put(reference, suffix);
            }
            first = false;

            if (stopHere.contains(reference)) {
                continue;
            }
            final AbstractVariable var = state.getAbstractVariable(reference);
            if (var == null) {
                continue;
            }
            if (var instanceof AbstractNumber) {
                continue;
            }
            if (var instanceof Array) {
                final Array array = (Array) var;

                if (primitives) {
                    if (allowedEdges == null || allowedEdges.contains(new ArrayLengthEdge())) {
                        final AbstractVariableReference lengthRef = array.getLength();
                        final NonRootPosition lengthPos = ArrayLengthPosition.create(suffix);
                        todo.add(new Pair<>(lengthRef, lengthPos));
                    }
                }

                if (array instanceof AbstractArray) {
                    continue;
                }
                final ConcreteArray concArr = (ConcreteArray) array;
                final int length = concArr.getLiteralLength();
                for (int index = 0; index < length; index++) {
                    final NonRootPosition pos = ArrayElementPosition.create(suffix, index);
                    final AbstractVariableReference childRef = concArr.get(state, reference, index);
                    if (!childRef.isNULLRef()) {
                        if (primitives || childRef.pointsToReferenceType()) {
                            if (allowedEdges == null || allowedEdges.contains(new ArrayMemberEdge(index))) {
                                todo.add(new Pair<>(childRef, pos));
                            }
                        }
                    }
                }
                continue;
            }
            if (var instanceof AbstractInstance) {
                continue;
            }
            if (var instanceof ConcreteInstance) {
                final ConcreteInstance ai = (ConcreteInstance) var;
                for (final Map.Entry<FieldIdentifier, AbstractVariableReference> entry : ai.getAllFields().entrySet()) {
                    if (entry.getValue() == null) {
                        continue;
                    }
                    if (entry.getKey().getFieldName().endsWith("!cycleJoint")) {
                        continue;
                    }
                    final NonRootPosition pos = InstanceFieldPosition.create(suffix, entry.getKey());
                    final AbstractVariableReference childRef = entry.getValue();
                    if (!childRef.isNULLRef()) {
                        if (primitives || childRef.pointsToReferenceType()) {
                            if (allowedEdges == null || allowedEdges.contains(new InstanceFieldEdge(entry.getKey()))) {
                                todo.add(new Pair<>(childRef, pos));
                            }
                        }
                    }
                }
            }
        }
        return result;
    }

    /**
     * Attention:
     * <ul>
     * <li>ref is not returned if it does not reach itself</li>
     * </ul>
     * @param ref a reference which must not point to a primitive value
     * @param primitives references to primitive values are returned iff this is set
     * @param stopHere do not go through these references
     * @param state the state in which we want to look
     * @return all references reachable from ref in state, does not contain null references.
     */
    public static Collection<AbstractVariableReference> getReachableRefs(
        final AbstractVariableReference ref,
        final boolean primitives,
        final Collection<AbstractVariableReference> stopHere,
        final State state)
    {
        return new LinkedHashSet<>(Reachability.getReachableRefsWithSuffix(ref, primitives, stopHere, null, state).keySet());
    }

    /**
     * @param state a state
     * @param refFrom a reference
     * @param fieldSet a set of fields
     * @return A map containing all references that are reachable when starting in refFrom and going along the
     * given fields as keys. The values indicate whether the path has at least length one or not.
     */
    public static Map<AbstractVariableReference, Boolean> getReachableRefs(
        final State state,
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fieldSet)
    {
        final Collection<Pair<AbstractVariableReference, Boolean>> done = new LinkedHashSet<>();
        final LinkedList<Pair<AbstractVariableReference, Boolean>> todo = new LinkedList<>();
        todo.add(new Pair<>(refFrom, false));
        final Map<AbstractVariableReference, Boolean> result = new LinkedHashMap<>();
        while (!todo.isEmpty()) {
            final Pair<AbstractVariableReference, Boolean> pair = todo.pop();
            if (!done.add(pair)) {
                continue;
            }
            final boolean didOneStep = pair.y;
            final AbstractVariableReference currentStart = pair.x;
            result.put(currentStart, didOneStep);
            final Collection<Pair<AbstractVariableReference, Boolean>> concretelyReachedPairs = new LinkedHashSet<>();
            // get all references reachable by only following the fields
            for (final AbstractVariableReference reachedRef : Reachability.followFields(currentStart, fieldSet, state)) {
                final boolean reachedUsingField =
                    didOneStep
                        || !reachedRef.equals(currentStart)
                        || reachedRef.equals(Reachability.followFields(currentStart, fieldSet, reachedRef, true, state));
                concretelyReachedPairs.add(new Pair<>(reachedRef, reachedUsingField));
            }
            todo.addAll(concretelyReachedPairs);

            // for all reachable references also follow each fitting defreach annotation
            for (final Pair<AbstractVariableReference, Boolean> reachedPair : concretelyReachedPairs) {
                final AbstractVariableReference reachedRef = reachedPair.x;
                final boolean reachedUsingOneStep = reachedPair.y;
                for (final DefiniteReachabilityAnnotation defReach : state
                    .getHeapAnnotations()
                    .getDefiniteReachabilities()
                    .getAnnotations(reachedRef, fieldSet))
                {
                    todo.add(new Pair<>(defReach.getTo(), reachedUsingOneStep || defReach.isAtLeastOneStep()));
                }
            }
        }
        return result;
    }

    /**
     * @param state a state
     * @param refFrom a reference
     * @param fieldSet a set of fields
     * @param atLeastOneStep whether the past must have at least length one
     * @return all references that are reachable when starting in refFrom and going along the
     * given fields.
     */
    public static Collection<AbstractVariableReference> getReachableRefs(
        final State state,
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fieldSet,
        final boolean atLeastOneStep)
    {
        final Map<AbstractVariableReference, Boolean> reachableRefs = Reachability.getReachableRefs(state, refFrom, fieldSet);
        if (!atLeastOneStep) {
            return reachableRefs.keySet();
        }
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final Entry<AbstractVariableReference, Boolean> entry : reachableRefs.entrySet()) {
            final AbstractVariableReference key = entry.getKey();
            if (entry.getValue()) {
                result.add(key);
            }
        }
        return result;
    }

    /**
     * @param state check whether the connection is valid in this state
     * @param refFrom start of the connection
     * @param fieldSet fields used by the connection
     * @param refTo end of the connection
     * @param atLeastOneStep whether the connection must have at least length one
     * @return whether the specified connection exists in <code>state</code> or not
     */
    public static boolean areConnected(
        final State state,
        final AbstractVariableReference refFrom,
        final Set<HeapEdge> fieldSet,
        final AbstractVariableReference refTo,
        final boolean atLeastOneStep)
    {
        return Reachability.getReachableRefs(state, refFrom, fieldSet, atLeastOneStep).contains(refTo);
    }

    /**
     * checks whether the connection from otherHeapPositions described by the parameters might also exist in heapPositions
     * using defReach-, equality- and joins-annotations
     * @param heapPositions check whether the described connection is valid for these heap-positions
     * @param otherHeapPositions w.r.t these heap-positions, the described connection is valid
     * @param fromReference start of the connection; reference from <code>otherHeapPositions</code>
     * @param toReference end of the connection; reference from <code>otherHeapPositions</code>
     * @param fields set of fields used by the connection
     * @return true if the described connection might exist in heapPositions, false otherwise
     */
    public static boolean checkReachabilityUsingAnnotations(
        final HeapPositions heapPositions,
        final HeapPositions otherHeapPositions,
        final AbstractVariableReference fromReference,
        final AbstractVariableReference toReference,
        final Set<HeapEdge> fields)
    {
        final Set<StatePosition> fromPositions = new HashSet<>(otherHeapPositions.getPositionsForRef(fromReference));
        final Set<StatePosition> toAdd = new HashSet<>();
        final Iterator<StatePosition> fromIterator = fromPositions.iterator();
        while (fromIterator.hasNext()) {
            final StatePosition from = fromIterator.next();
            if (!heapPositions.hasPosition(from)) {
                final Collection<PrefixResult> prefixes =
                    heapPositions.getMaxRealizedPrefixes(from, otherHeapPositions);
                for (final PrefixResult prefix : prefixes) {
                    toAdd.add(prefix.getPosition());
                }
                fromIterator.remove();
            }
        }
        fromPositions.addAll(toAdd);
        toAdd.clear();
        for (final StatePosition from : fromPositions) {
            final Set<StatePosition> toPositions = new HashSet<>(otherHeapPositions.getPositionsForRef(toReference));
            final Iterator<StatePosition> toIterator = toPositions.iterator();
            while (toIterator.hasNext()) {
                final StatePosition to = toIterator.next();
                if (!heapPositions.hasPosition(to)) {
                    final Collection<PrefixResult> prefixes =
                        heapPositions.getMaxRealizedPrefixes(to, otherHeapPositions);
                    for (final PrefixResult prefix : prefixes) {
                        toAdd.add(prefix.getPosition());
                    }
                    toIterator.remove();
                }
            }
            toPositions.addAll(toAdd);
            for (final StatePosition to : toPositions) {
                final AbstractVariableReference fromRef = heapPositions.getReferenceForPos(from);
                final AbstractVariableReference reachedRef =
                    Reachability.followFields(fromRef, fields, heapPositions.getReferenceForPos(to), false, heapPositions.getState());
                if (reachedRef == null) {
                    continue;
                }
                final AbstractVariableReference toRef = heapPositions.getReferenceForPos(to);
                if (reachedRef.equals(toRef)) {
                    return true;
                }
                if (heapPositions.getState().getHeapAnnotations().getJoiningStructures().areJoining(reachedRef, toRef))
                {
                    return true;
                }
                if (heapPositions
                    .getState()
                    .getHeapAnnotations()
                    .getEqualityGraph()
                    .areMarkedAsPossiblyEqual(reachedRef, toRef)
                    && !fromRef.equals(reachedRef))
                {
                    return true;
                }
            }
        }
        return false;
    }

}
