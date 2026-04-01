package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * An annotation of this class gives information about the existence of some connection in the heap.
 *
 * For x -F!!-> y we know that there is a path starting in reference x to reference y that only uses fields given in
 * the set F. The described path must have at least length one (even if x and y are the same).
 *
 * For x -F!-> y we know the same, but here the path may also have length 0.
 */
public class DefiniteReachabilityAnnotation {
    /**
     * The reference where the path starts.
     */
    private final AbstractVariableReference from;

    /**
     * The reference where the path leads to.
     */
    private final AbstractVariableReference to;

    /**
     * The only fields that may be used on the path.
     */
    private final Set<HeapEdge> fields;

    /**
     * True only if we know that the path has at least one step.
     */
    private final boolean atLeastOneStep;

    /**
     * This annotation says, that there exists a path from <code>from</code> to
     * <code>to</code> using a field unambiguously selected by <code>fields</code>
     * for each step. If <code>from</code> == <code>to</code>, then the end of the
     * path has been reached and the annotation needs to be discarded. But to allow
     * the description of a cycle, there is one exception to this rule: If
     * <code>atLeastOneStep</code> is set, then the remaining path has at least a
     * length of one.
     * @param fromParam See above.
     * @param toParam See above.
     * @param fieldsParam See above.
     * @param atLeastOneStepParam See above.
     * @param classPath Only used for sanity check of fields.
     */
    public DefiniteReachabilityAnnotation(
        final AbstractVariableReference fromParam,
        final AbstractVariableReference toParam,
        final Set<HeapEdge> fieldsParam,
        final boolean atLeastOneStepParam,
        final ClassPath classPath)
    {
        assert !fromParam.isNULLRef() && !toParam.isNULLRef() : "DefiniteReachabilityAnnotation creation with null reference";
        assert InstanceFieldEdge.fieldsAreDeterministic(fieldsParam, classPath) : "DefiniteReachabilityAnnotation creation with nondeterministic fields";
        assert !fromParam.equals(toParam) || atLeastOneStepParam : "Creation of DefiniteReachabilityAnnotation at end of path";
        assert (toParam.pointsToReferenceType());
        this.from = fromParam;
        this.to = toParam;
        this.fields = fieldsParam;
        this.atLeastOneStep = atLeastOneStepParam;
    }

    /**
     * @return the reference from which the path starts
     */
    public AbstractVariableReference getFrom() {
        return this.from;
    }

    /**
     * @return the reference where the path leads to
     */
    public AbstractVariableReference getTo() {
        return this.to;
    }

    /**
     * @return the only fields that may be used on the path
     */
    public Set<HeapEdge> getFields() {
        return this.fields;
    }

    /**
     * @return true only if we know that the path uses at least one field.
     */
    public boolean isAtLeastOneStep() {
        return this.atLeastOneStep;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.atLeastOneStep ? 1231 : 1237);
        result = prime * result + ((this.fields == null) ? 0 : this.fields.hashCode());
        result = prime * result + ((this.from == null) ? 0 : this.from.hashCode());
        result = prime * result + ((this.to == null) ? 0 : this.to.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final DefiniteReachabilityAnnotation other = (DefiniteReachabilityAnnotation) obj;
        if (this.atLeastOneStep != other.atLeastOneStep) {
            return false;
        }
        if (this.fields == null) {
            if (other.fields != null) {
                return false;
            }
        } else if (!this.fields.equals(other.fields)) {
            return false;
        }
        if (this.from == null) {
            if (other.from != null) {
                return false;
            }
        } else if (!this.from.equals(other.from)) {
            return false;
        }
        if (this.to == null) {
            if (other.to != null) {
                return false;
            }
        } else if (!this.to.equals(other.to)) {
            return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.from.toString()
            + " -"
            + this.fields.toString()
            + "-"
            + (this.atLeastOneStep ? "!!" : "!")
            + "> "
            + this.to.toString();
    }

    /**
     * @param thatAnnotation a DefReach annotation
     * @return true if "from" and "to" are the same
     */
    public boolean isBetweenSameReferencesAs(final DefiniteReachabilityAnnotation thatAnnotation) {
        return this.from.equals(thatAnnotation.getFrom()) && this.to.equals(thatAnnotation.getTo());
    }

    /**
     * @param originHeapPositions some HeapPositions
     * @param targetHeapPositions other HeapPositions, that might have some connections in common with <code>originHeapPositions</code>
     * @return defreach-annotations for <code>targetHeapPositions</code>, describing connections that were found in <code>originHeapPositions</code> and also exist in <code>targetHeapPositions</code>
     */
    public static Set<DefiniteReachabilityAnnotation> getCommonConnections(
        final HeapPositions originHeapPositions,
        final HeapPositions targetHeapPositions)
    {
        final Set<DefiniteReachabilityAnnotation> commonConnections = new LinkedHashSet<>();
        commonConnections.addAll(DefiniteReachabilityAnnotation.getCommonConnectionsFromRealizedPaths(originHeapPositions, targetHeapPositions));
        commonConnections.addAll(DefiniteReachabilityAnnotation.getCommonConnectionsBasedOnAnnotations(originHeapPositions, targetHeapPositions));
        return commonConnections;
    }

    /**
     * @param originHeapPositions some HeapPositions
     * @param targetHeapPositions other HeapPositions, that might have some connections in common with <code>originHeapPositions</code>
     * @return defreach-annotations for <code>targetHeapPositions</code>, describing connections that are realized in <code>originHeapPositions</code> and also exist in <code>targetHeapPositions</code>
     */
    private static Set<DefiniteReachabilityAnnotation> getCommonConnectionsFromRealizedPaths(
        final HeapPositions originHeapPositions,
        final HeapPositions targetHeapPositions)
    {
        final Set<DefiniteReachabilityAnnotation> commonConnections = new LinkedHashSet<>();
        final State state = originHeapPositions.getState();
        for (final Map.Entry<AbstractVariableReference, Collection<StatePosition>> e : originHeapPositions
            .getRefsWithMultiplePositions()
            .entrySet())
        {
            final Collection<StatePosition> positions = e.getValue();
            if (state.getHeapAnnotations().isMaybeExisting(e.getKey())) {
                continue;
            }
            commonConnections.addAll(DefiniteReachabilityAnnotation.createDefiniteReachabilityAnnotationsBetweenPositions(
                positions,
                positions,
                (DefiniteReachabilityAnnotation) null,
                originHeapPositions,
                targetHeapPositions));
        }
        return commonConnections;
    }

    /**
     * @param originHeapPositions some HeapPositions
     * @param targetHeapPositions other HeapPositions, that might have some connections in common with <code>originHeapPositions</code>
     * @return defreach-annotations for <code>targetHeapPositions</code>, describing connections that also exist in <code>originHeapPositions</code> as defreach-annotations
     */
    private static Set<DefiniteReachabilityAnnotation> getCommonConnectionsBasedOnAnnotations(
        final HeapPositions originHeapPositions,
        final HeapPositions targetHeapPositions)
    {
        final Set<DefiniteReachabilityAnnotation> commonConnections = new LinkedHashSet<>();
        final State state = originHeapPositions.getState();
        for (final DefiniteReachabilityAnnotation annotation : state.getHeapAnnotations().getDefiniteReachabilities()) {
            if (state.getHeapAnnotations().isMaybeExisting(annotation.getFrom())
                || state.getHeapAnnotations().isMaybeExisting(annotation.getTo()))
            {
                continue;
            }
            commonConnections.addAll(DefiniteReachabilityAnnotation.createDefiniteReachabilityAnnotationsBetweenPositions(
                originHeapPositions.getPositionsForRef(annotation.getFrom()),
                originHeapPositions.getPositionsForRef(annotation.getTo()),
                annotation,
                originHeapPositions,
                targetHeapPositions));
        }

        return commonConnections;
    }

    /**
     * For each pair (x, y) from fromPositions \times toPositions we know that
     * the reference at position x definitely reaches the reference at position
     * y using the fields from existingAnnotation. For those pairs where the
     * connection is not already concretely existing in the target state we
     * create a new annotation.
     * @param fromPositions some positions
     * @param toPositions some positions
     * @param existingAnnotation an existing annotation describing the
     * connection (or null)
     * @param originHeapPositions the heap positions for the state where we
     * found the definite connections
     * @param heapPosTarget heap positions for the state where we want to add
     * the annotations
     * @return annotations (with references from the target state) that are
     * based on the connections found in the origin state
     */
    public static Set<DefiniteReachabilityAnnotation> createDefiniteReachabilityAnnotationsBetweenPositions(
        final Collection<StatePosition> fromPositions,
        final Collection<StatePosition> toPositions,
        final DefiniteReachabilityAnnotation existingAnnotation,
        final HeapPositions originHeapPositions,
        final HeapPositions heapPosTarget)
    {
        final Set<DefiniteReachabilityAnnotation> annotations = new LinkedHashSet<>();
        for (final StatePosition fromPosition : fromPositions) {
            for (final PrefixResult fromPositionPrefix : heapPosTarget.getMaxRealizedPrefixes(
                fromPosition,
                originHeapPositions))
            {
                final AbstractVariableReference fromReference = fromPositionPrefix.getReference();
                final Set<HeapEdge> fields = new LinkedHashSet<>();
                boolean atLeastOneStep = false;
                if (existingAnnotation != null) {
                    fields.addAll(existingAnnotation.getFields());
                    atLeastOneStep = existingAnnotation.isAtLeastOneStep();
                }
                if (!fromPositionPrefix.isRealized()) {
                    if (fromPositionPrefix.getUnrealizedPosition() == null) {
                        continue;
                    }
                    fields.addAll(fromPositionPrefix.getUnrealizedPosition().getHeapEdges());
                    atLeastOneStep = true;
                }
                if (!InstanceFieldEdge.fieldsAreDeterministic(fields, heapPosTarget.getState().getClassPath())) {
                    continue;
                }

                for (final StatePosition toPosition : toPositions) {
                    final AbstractVariableReference toReference = heapPosTarget.getReferenceForPos(toPosition, true);
                    if (toReference == null || (fromReference.equals(toReference) && !atLeastOneStep)) {
                        continue;
                    }

                    annotations.add(new DefiniteReachabilityAnnotation(
                        fromReference,
                        toReference,
                        fields,
                        atLeastOneStep,
                        heapPosTarget.getState().getClassPath()));
                }
            }
        }
        return annotations;
    }

    public String toSExpString() {
        final StringBuilder s = new StringBuilder();
        if (this.atLeastOneStep) {
            s.append("(definite-reachability-non-empty ");
        } else {
            s.append("(definite-reachability-maybe-empty ");
        }
        s.append(this.from.toString());
        s.append(this.to.toString());
        s.append(" (");
        boolean firstField = true;
        for (HeapEdge f : this.getFields()) {
            if (firstField) {
                firstField = false;
            } else {
                s.append(" ");
            }
            s.append(f.getIdentifier().toString());
        }
        s.append("))");
        return s.toString();
    }
}
