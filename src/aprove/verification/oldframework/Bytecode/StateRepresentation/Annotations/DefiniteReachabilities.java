package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * container for all defreach-annotations that exist in one state
 * note that this class holds some indices that have to be updated whenever annotations are added or removed
 */
public class DefiniteReachabilities implements Iterable<DefiniteReachabilityAnnotation>, Cloneable {

    /**
     * Iterator for the defreach-annotations contained in one {@link DefiniteReachabilities} instance
     */
    private class DefReachIterator implements Iterator<DefiniteReachabilityAnnotation> {

        /**
         * Iterator for the undelying collection that stores the defreach-annotations
         */
        private final Iterator<DefiniteReachabilityAnnotation> it = DefiniteReachabilities.this.definiteReachabilities
            .iterator();

        /**
         * the last defreach-annotation that was returned by a call to {@link DefReachIterator#next()}
         */
        private DefiniteReachabilityAnnotation previous;

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean hasNext() {
            return this.it.hasNext();
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public DefiniteReachabilityAnnotation next() {
            this.previous = this.it.next();
            return this.previous;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public void remove() {
            DefiniteReachabilities.this.removeFromIndex(this.previous);
            this.it.remove();
        }

    }

    /**
     * The known definite reachability informations.
     */
    private final Set<DefiniteReachabilityAnnotation> definiteReachabilities = new LinkedHashSet<>();

    /**
     * indexs the defreach-annotations by the start-reference
     */
    private final Map<AbstractVariableReference, Set<DefiniteReachabilityAnnotation>> index = new LinkedHashMap<>();

    /**
     * indexes the defreach-annotations by the target-reference
     */
    private final Map<AbstractVariableReference, Set<DefiniteReachabilityAnnotation>> reversedIndex =
        new LinkedHashMap<>();

    /**
     * create new {@link DefiniteReachabilities} instance
     */
    public DefiniteReachabilities() {
    }

    /**
     * @param annotations defreach-annotations to copy into the new {@link DefiniteReachabilities} instance
     */
    public DefiniteReachabilities(final Set<DefiniteReachabilityAnnotation> annotations) {
        this.addAll(annotations);
    }

    /**
     * must be called whenever a defreach-annotation is added!!!
     * @param annotation defreach-annotation that should be added to all indices
     */
    private void addToIndex(final DefiniteReachabilityAnnotation annotation) {
        Set<DefiniteReachabilityAnnotation> annotations =
            this.index.containsKey(annotation.getFrom())
                ? this.index.get(annotation.getFrom())
                    : new LinkedHashSet<DefiniteReachabilityAnnotation>();
        annotations.add(annotation);
        this.index.put(annotation.getFrom(), annotations);
        annotations =
            this.reversedIndex.containsKey(annotation.getTo())
                ? this.reversedIndex.get(annotation.getTo())
                    : new LinkedHashSet<DefiniteReachabilityAnnotation>();
        this.reversedIndex.put(annotation.getTo(), annotations);
    }

    /**
     * When identifying oldRef and newRef and replacing oldRef by newRef, compute new definite reaches information and
     * return information about these changes that can be used when constructing the TRS.
     * @param s the current state
     * @param oldRef the reference that will be replaced
     * @param newRef the replacement reference
     * @return information about the relation of the definite reaches annotations
     */
    public Collection<DefiniteReachabilityAnnotationCreation> replaceReference(
        final State s,
        final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef)
    {
        if (oldRef.equals(newRef)) {
            return Collections.emptyList();
        }
        final Collection<DefiniteReachabilityAnnotationCreation> res = new LinkedList<>();
        final Iterator<DefiniteReachabilityAnnotation> it = this.iterator();
        final List<DefiniteReachabilityAnnotation> newReachabilities = new ArrayList<>();
        while (it.hasNext()) {
            final DefiniteReachabilityAnnotation reachability = it.next();
            if (reachability.getFrom().equals(oldRef)) {
                it.remove();
                final AbstractVariableReference newFrom =
                    Reachability.followFields(newRef, reachability.getFields(), reachability.getTo(), false, s);
                // was at least one step and no fields followed
                final boolean isAtLeastOneStep =
                    reachability.isAtLeastOneStep() && newFrom != null && newFrom.equals(newRef);
                if (newFrom != null
                    && !newFrom.isNULLRef()
                    && (!newFrom.equals(reachability.getTo()) || isAtLeastOneStep))
                {
                    final AbstractVariableReference newTo =
                        reachability.getTo().equals(oldRef) ? newRef : reachability.getTo();
                    final DefiniteReachabilityAnnotation newReachability =
                        new DefiniteReachabilityAnnotation(
                            newFrom,
                            newTo,
                            reachability.getFields(),
                            isAtLeastOneStep,
                            s.getClassPath());
                    newReachabilities.add(newReachability);
                    assert (!s.getHeapAnnotations().isMaybeExisting(newReachability.getTo()));
                    // we followed some fields
                    if (!newFrom.equals(newRef)) {
                        res.add(new DefiniteReachabilityAnnotationCreation(
                            reachability,
                            newReachability,
                            IntegerRelationType.LT));
                    }
                }
            } else if (reachability.getTo().equals(oldRef)) {
                it.remove();
                if (!reachability.getFrom().equals(newRef) || reachability.isAtLeastOneStep()) {
                    final DefiniteReachabilityAnnotation newReachability =
                        new DefiniteReachabilityAnnotation(
                            reachability.getFrom(),
                            newRef,
                            reachability.getFields(),
                            reachability.isAtLeastOneStep(),
                            s.getClassPath());
                    newReachabilities.add(newReachability);
                    assert (!s.getHeapAnnotations().isMaybeExisting(newReachability.getTo()));
                }
            }
        }
        this.addAll(newReachabilities);
        return res;
    }

    /**
     * @return all references that are either start- or target of a defreach-annotation
     */
    public Collection<? extends AbstractVariableReference> getReferences() {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final DefiniteReachabilityAnnotation defReach : this) {
            result.add(defReach.getFrom());
            result.add(defReach.getTo());
        }
        return result;
    }

    /**
     * @param references if either the start or the target of a defreach-annotation is contained in this list, the defreach annotation is removed
     */
    public void removeAnnotationsContainingReferences(final AbstractVariableReference... references) {
        final Iterator<DefiniteReachabilityAnnotation> it = this.iterator();
        while (it.hasNext()) {
            final DefiniteReachabilityAnnotation defReach = it.next();
            for (final AbstractVariableReference ref : references) {
                if (defReach.getFrom().equals(ref) || defReach.getTo().equals(ref)) {
                    it.remove();
                    break;
                }
            }
        }
    }

    /**
     * @param annotation annotation to be removed
     */
    public void remove(final DefiniteReachabilityAnnotation annotation) {
        this.definiteReachabilities.remove(annotation);
        this.removeFromIndex(annotation);
    }

    /**
     * @param annotations annotations to be remomved
     */
    public void removeAll(final Collection<DefiniteReachabilityAnnotation> annotations) {
        for (final DefiniteReachabilityAnnotation annotation : annotations) {
            this.remove(annotation);
        }
    }

    /**
     * call this every time a defreach-annotaion is removed!!!
     * @param annotation annotation to be removed from all indices
     */
    private void removeFromIndex(final DefiniteReachabilityAnnotation annotation) {
        if (this.index.containsKey(annotation.getFrom())) {
            this.index.get(annotation.getFrom()).remove(annotation);
        }
        if (this.reversedIndex.containsKey(annotation.getTo())) {
            this.reversedIndex.get(annotation.getTo()).remove(annotation);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public DefiniteReachabilities clone() {
        return new DefiniteReachabilities(this.definiteReachabilities);
    }

    /**
     * @param annotation annotation to add
     * @return false, if the given annotation was already there, true otherwise
     */
    public boolean add(final DefiniteReachabilityAnnotation annotation) {
        this.addToIndex(annotation);
        return this.definiteReachabilities.add(annotation);
    }

    /**
     * @param annotations annotations to add
     */
    public void addAll(final Collection<DefiniteReachabilityAnnotation> annotations) {
        for (final DefiniteReachabilityAnnotation defReach : annotations) {
            this.add(defReach);
        }
    }

    /**
     * @param startRef start of the annotations we are interested in
     * @return all annotations starting in <code>startRef</code>
     */
    public Set<DefiniteReachabilityAnnotation> getDefReachesByStartRef(final AbstractVariableReference startRef) {
        return this.getFromIndex(startRef);
    }

    /**
     * @param targetRef target of the annotations we are interested in
     * @return all annotations ending in <code>targetRef</code>
     */
    public Set<DefiniteReachabilityAnnotation> getDefReachesByTargetRef(final AbstractVariableReference targetRef) {
        return this.getFromReversedIndex(targetRef);
    }

    /**
     * @param originHeapPositions <code>HeapPositions</code> object containing the annotations to check
     * @param heapPositionsToCheck <code>HeapPositions</code> object for which the annotations should be checked
     * @throws IntersectionFailException if a definite connection can definitely not exist in <code>heapPositionsToCheck</code>
     */
    public static void checkDefiniteReaches(
        final HeapPositions originHeapPositions,
        final HeapPositions heapPositionsToCheck) throws IntersectionFailException
    {
        for (final DefiniteReachabilityAnnotation annotation : originHeapPositions
            .getState()
            .getHeapAnnotations()
            .getDefiniteReachabilities())
        {
            if (!Reachability.checkReachabilityUsingAnnotations(
                heapPositionsToCheck,
                originHeapPositions,
                annotation.getFrom(),
                annotation.getTo(),
                annotation.getFields()))
            {
                throw new IntersectionFailException("annotation "
                    + annotation
                    + " is not valid for the state to intersect with");
            }
        }
    }

    /**
     * tries to generate valid defreach-annotations for the given <code>HeapPositions</code>
     * adds the annotation b-{f}!->c if we have a-{f}!->c and a-f->b; moreover, the annotation a-{f}!->c is removed
     * @param heapPositions <code>HeapPositions</code> we want to generate new defreach-annotations for
     * @return the defreach-annotations that were generated
     */
    public static Set<DefiniteReachabilityAnnotation> generateAdditionalAnnotations(final HeapPositions heapPositions) {
        final State state = heapPositions.getState();
        final Set<DefiniteReachabilityAnnotation> toAdd = new HashSet<>();
        final ClassPath classPath = state.getClassPath();
        final EqualityGraph equalityGraph = state.getHeapAnnotations().getEqualityGraph();
        final DefiniteReachabilities annotations = state.getHeapAnnotations().getDefiniteReachabilities();
        final Iterator<DefiniteReachabilityAnnotation> it = annotations.iterator();
        while (it.hasNext()) {
            final DefiniteReachabilityAnnotation annotation = it.next();
            final AbstractVariableReference to = annotation.getTo();
            final AbstractVariableReference from = annotation.getFrom();
            final Set<HeapEdge> fields = annotation.getFields();
            for (final AbstractVariableReference partner : equalityGraph.getPartners(to)) {
                if (Reachability.areConnected(state, from, fields, partner, false)
                    && !Reachability.areConnected(state, partner, fields, to, false))
                {
                    toAdd.add(new DefiniteReachabilityAnnotation(partner, to, fields, false, classPath));
                    it.remove();
                    break;
                }
            }
        }
        annotations.addAll(toAdd);
        return toAdd;
    }

    /**
     * delete all annotations
     */
    public void clear() {
        this.definiteReachabilities.clear();
        this.index.clear();
        this.reversedIndex.clear();
    }

    /**
     * @param startRef start-reference of the annotation we want to get
     * @return all annotations starting at the given reference
     */
    private Set<DefiniteReachabilityAnnotation> getFromIndex(final AbstractVariableReference startRef) {
        return this.index.containsKey(startRef) ? this.index.get(startRef) : Collections
            .<DefiniteReachabilityAnnotation>emptySet();
    }

    /**
     * @param targetRef target-reference of the annotations we want to get
     * @return all annotations ending at the given reference
     */
    private Set<DefiniteReachabilityAnnotation> getFromReversedIndex(final AbstractVariableReference targetRef) {
        return this.reversedIndex.containsKey(targetRef) ? this.reversedIndex.get(targetRef) : Collections
            .<DefiniteReachabilityAnnotation>emptySet();
    }

    /**
     * @param startRef the start-reference of the connection
     * @param targetRef the target-reference of the connection
     * @param fields the fields to use
     * @return whether there is an annotation that connects <code>startRef</code> and <code>targetRef</code> using <code>fields</code>
     */
    public boolean areConnected(
        final AbstractVariableReference startRef,
        final AbstractVariableReference targetRef,
        final ImmutableSet<HeapEdge> fields)
    {
        for (final DefiniteReachabilityAnnotation defReach : this.getFromIndex(startRef)) {
            assert (defReach.getFrom().equals(startRef));
            if (defReach.getTo().equals(targetRef)
                && defReach.getFields().containsAll(fields)
                && fields.containsAll(defReach.getFields()))
            {
                return true;
            }
        }
        return false;
    }

    /**
     * @param startRef the start-reference of the connection
     * @param targetRef the target-reference of the connection
     * @return whether there is an annotation that connects <code>startRef</code> and <code>targetRef</code> using any fields
     */
    public boolean areConnected(
            final AbstractVariableReference startRef,
            final AbstractVariableReference targetRef)
    {
        for (final DefiniteReachabilityAnnotation defReach : this.getFromIndex(startRef)) {
            assert (defReach.getFrom().equals(startRef));
            if (defReach.getTo().equals(targetRef)) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Iterator<DefiniteReachabilityAnnotation> iterator() {
        return new DefReachIterator();
    }

    /**
     * @param startRef the start-reference of the annotations we want to get
     * @param fields the fields used by the annotations we want to get
     * @return all annotations starting in <code>startRef</code> that use (a subset of) the given <code>fields</code>
     */
    public Set<DefiniteReachabilityAnnotation> getAnnotations(
        final AbstractVariableReference startRef,
        final Set<HeapEdge> fields)
    {
        final Set<DefiniteReachabilityAnnotation> res = new LinkedHashSet<>();
        for (final DefiniteReachabilityAnnotation annotation : this.getFromIndex(startRef)) {
            if (fields.containsAll(annotation.getFields())) {
                res.add(annotation);
            }
        }
        return res;
    }

    public Set<DefiniteReachabilityAnnotation> getAnnotations(
            final AbstractVariableReference startRef,
            final AbstractVariableReference endRef) {
        return this.getFromIndex(startRef)
                   .stream()
                   .filter(annotation -> annotation.getTo() == endRef)
                   .collect(Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * Clean the DefiniteReachability information in the given state.
     * @param s the state to clean
     * @param refsToRemove the references that will not exist anymore after the gc()
     * @return a pair where the first component is true if we removed any DefReach annotation. The second component
     * gives information about new DefReach annotations that were created.
     *
     */
    public static Pair<Boolean, Set<VariableInformation>> gc(
        final State s,
        final Collection<AbstractVariableReference> refsToRemove)
    {
        final HeapAnnotations heapAnnotations = s.getHeapAnnotations();
        final DefiniteReachabilities definiteReachabilities = heapAnnotations.getDefiniteReachabilities();

        boolean annotationRemoved = false;
        final Set<VariableInformation> annotationChanges = new LinkedHashSet<>();
        final Set<DefiniteReachabilityAnnotation> replacementReachabilities = new LinkedHashSet<>();

        // create new defreach annotations
        for (final DefiniteReachabilityAnnotation reachability : definiteReachabilities) {
            AbstractVariableReference from = reachability.getFrom();
            AbstractVariableReference to = reachability.getTo();
            // only "to" is removed
            if (refsToRemove.contains(to) && !refsToRemove.contains(from)) {
                /*
                 * We do not have from -!-> to anymore, but maybe we can add from -!-> x for a reference x that is
                 * reachable from "to".
                 */
                if (s.getAbstractVariable(to) instanceof ConcreteInstance) {
                    ConcreteInstance var = (ConcreteInstance) s.getAbstractVariable(to);
                    for (Entry<FieldIdentifier, AbstractVariableReference> entry : var.getAllFields().entrySet()) {
                        AbstractVariableReference newTo = entry.getValue();
                        FieldIdentifier field = entry.getKey();
                        Set<HeapEdge> fields = new LinkedHashSet<>(reachability.getFields());
                        fields.add(new InstanceFieldEdge(field));
                        if (heapAnnotations.isMaybeExisting(newTo) || newTo.isNULLRef()
                            || !newTo.pointsToReferenceType()
                            || refsToRemove.contains(newTo)
                            || !InstanceFieldEdge.fieldsAreDeterministic(fields, s.getClassPath())) {
                            continue;
                        }
                        DefiniteReachabilityAnnotation newDRA = new DefiniteReachabilityAnnotation(from,
                                newTo,
                                fields,
                                true,
                                s.getClassPath());
                        if (replacementReachabilities.add(newDRA)) {
                            annotationChanges.add(new DefiniteReachabilityAnnotationCreation(reachability,
                                    newDRA,
                                    IntegerRelationType.GT));
                        }
                    }
                }
            }
        }

        // remove annotations where the source is fully realized
        Iterator<DefiniteReachabilityAnnotation> defReachIt = definiteReachabilities.iterator();
        while (defReachIt.hasNext()) {
            final DefiniteReachabilityAnnotation reachability = defReachIt.next();
            if (!refsToRemove.contains(reachability.getFrom()) && s.isFullyRealized(reachability.getFrom())) {
                annotationRemoved = true;
                defReachIt.remove();
            }
        }

        /*
         * Throw out all defreach annotations where we already have a realized field which is
         * part of the described path.
         */
        defReachIt = definiteReachabilities.iterator();
        while (defReachIt.hasNext()) {
            final DefiniteReachabilityAnnotation reachability = defReachIt.next();
            final AbstractVariableReference reachedRef =
                Reachability.followFields(
                    reachability.getFrom(),
                    reachability.getFields(),
                    new LinkedHashSet<AbstractVariableReference>(),
                    null,
                    false,
                    s);
            if (!reachability.getFrom().equals(reachedRef)) {
                // we reached another reference or ran into a cycle
                annotationRemoved = true;
                defReachIt.remove();
            }
        }

        // remove the annotations that use removed references
        defReachIt = definiteReachabilities.iterator();
        while (defReachIt.hasNext()) {
            boolean removed = false;
            final DefiniteReachabilityAnnotation reachability = defReachIt.next();
            if (refsToRemove.contains(reachability.getFrom())) {
                defReachIt.remove();
                annotationRemoved = true;
                removed = true;
            }
            if (refsToRemove.contains(reachability.getTo())) {
                if (!removed) {
                    defReachIt.remove();
                    annotationRemoved = true;
                }
            }
        }
        definiteReachabilities.addAll(replacementReachabilities);

        // replace x -{n}!-> y by x -{n}!!-> y for all x != y without x =?= y
        defReachIt = definiteReachabilities.iterator();
        while (defReachIt.hasNext()) {
            final DefiniteReachabilityAnnotation reachability = defReachIt.next();
            if (reachability.isAtLeastOneStep()) {
                continue;
            }

            final AbstractVariableReference from = reachability.getFrom();
            final AbstractVariableReference to = reachability.getTo();
            if (from.equals(to)) {
                continue;
            }
            if (!heapAnnotations.getEqualityGraph().areMarkedAsPossiblyEqual(from, to)) {
                defReachIt.remove();
                final DefiniteReachabilityAnnotation newDRA =
                    new DefiniteReachabilityAnnotation(from, to, reachability.getFields(), true, s.getClassPath());
                replacementReachabilities.add(newDRA);
            }
        }
        definiteReachabilities.addAll(replacementReachabilities);

        // throw out x -!-> y if we also have x -!!-y
        defReachIt = definiteReachabilities.iterator();
        while (defReachIt.hasNext()) {
            final DefiniteReachabilityAnnotation reachability = defReachIt.next();
            if (reachability.isAtLeastOneStep()) {
                continue;
            }
            for (final DefiniteReachabilityAnnotation other : definiteReachabilities) {
                if (other.isAtLeastOneStep()
                    && other.isBetweenSameReferencesAs(reachability)
                    && other.getFields().containsAll(reachability.getFields()))
                {
                    defReachIt.remove();
                    break;
                }
            }
        }

        return new Pair<>(annotationRemoved, annotationChanges);
    }

    /**
     * checks whether the connection from originHeapPositions described by the parameters also exists in heapPositions
     * @param heapPositions check whether the described connection is valid for these heap-positions
     * @param originHeapPositions w.r.t these heap-positions, the described connection is valid
     * @param fromReference start of the connection; reference from <code>otherHeapPositions</code>
     * @param toReference end of the connection; reference from <code>otherHeapPositions</code>
     * @param atLeastOneStep whether the connection has at least length one
     * @param fields subset of the used fields; is other fields may be used as well, but the final field-set has to be deterministic
     * @return defreach-annotations for <code>heapPositions</code> that correspond to the connection described by <code>fromReference</code>,
     *  <code>toReference</code>, <code>atLeastOneStep</code> and <code>fields</code>
     */
    private static Set<DefiniteReachabilityAnnotation> checkReachabilityExtendingFieldset(
        final HeapPositions heapPositions,
        final HeapPositions originHeapPositions,
        final AbstractVariableReference fromReference,
        final AbstractVariableReference toReference,
        final boolean atLeastOneStep,
        final Set<HeapEdge> fields)
    {
        final Set<DefiniteReachabilityAnnotation> annotations = new HashSet<>();
        final Collection<StatePosition> fromPositions = originHeapPositions.getPositionsForRef(fromReference);
        final Set<AbstractVariableReference> toReferences = new LinkedHashSet<>();
        final State state = heapPositions.getState();
        final ClassPath originClassPath = originHeapPositions.getState().getClassPath();
        for (final StatePosition to : originHeapPositions.getPositionsForRef(toReference)) {
            if (!heapPositions.hasPosition(to)) {
                continue;
            }
            toReferences.add(heapPositions.getReferenceForPos(to));
        }
        for (final StatePosition from : fromPositions) {
            if (!heapPositions.hasPosition(from)) {
                continue;
            }
            final Map<StatePosition, Pair<Set<HeapEdge>, Boolean>> todo = new HashMap<>();
            for (final StatePosition pos : heapPositions.getPositionsForRef(heapPositions.getReferenceForPos(from))) {
                todo.put(pos, new Pair<>(fields, false));
            }
            final Map<AbstractVariableReference, Set<DefiniteReachabilityAnnotation>> defReachIndex =
                state.getHeapAnnotations().getDefiniteReachabilities().index;
            final Set<StatePosition> done = new HashSet<>();
            final Map<StatePosition, Pair<Set<HeapEdge>, Boolean>> toAdd = new HashMap<>();
            while (!todo.isEmpty()) {
                final Iterator<Map.Entry<StatePosition, Pair<Set<HeapEdge>, Boolean>>> it = todo.entrySet().iterator();
                while (it.hasNext()) {
                    final Map.Entry<StatePosition, Pair<Set<HeapEdge>, Boolean>> current = it.next();
                    it.remove();
                    final StatePosition reachablePos = current.getKey();
                    final AbstractVariableReference reachableRef = heapPositions.getReferenceForPos(reachablePos);
                    final Set<HeapEdge> currentFields = current.getValue().x;
                    final boolean didOneStep = current.getValue().y;
                    done.add(current.getKey());
                    if (defReachIndex.containsKey(reachableRef)) {
                        // make one step using a defreach-annotation
                        for (final DefiniteReachabilityAnnotation annotation : defReachIndex.get(reachableRef)) {
                            final Set<HeapEdge> newFields = new HashSet<>(currentFields);
                            newFields.addAll(annotation.getFields());
                            // give up if adding the fields of annotation <code>a</code> made the path non-deterministic
                            if (!InstanceFieldEdge.fieldsAreDeterministic(newFields, originClassPath)) {
                                continue;
                            }
                            final boolean oneStep = atLeastOneStep && (didOneStep || annotation.isAtLeastOneStep());
                            if (toReferences.contains(annotation.getTo())
                                && (oneStep || !fromReference.equals(toReference)))
                            {
                                annotations.add(new DefiniteReachabilityAnnotation(
                                    fromReference,
                                    toReference,
                                    newFields,
                                    oneStep,
                                    originClassPath));
                            } else {
                                for (final StatePosition pos : heapPositions.getPositionsForRef(annotation.getTo())) {
                                    if (!done.contains(pos)) {
                                        toAdd.put(
                                            pos,
                                            new Pair<>(newFields, didOneStep || annotation.isAtLeastOneStep()));
                                    }
                                }
                            }
                        }
                    }
                    final AbstractVariable var = state.getAbstractVariable(reachableRef);
                    if (!(var instanceof ConcreteInstance)) {
                        continue;
                    }
                    // make one step using fields
                    for (final Entry<FieldIdentifier, AbstractVariableReference> e : ((ConcreteInstance) var)
                        .getAllFields()
                        .entrySet())
                    {
                        if (e.getValue().isNULLRef()) {
                            continue;
                        }
                        final Set<HeapEdge> newFields = new HashSet<>(currentFields);
                        newFields.add(new InstanceFieldEdge(e.getKey()));
                        // give up if adding the fields of annotation <code>a</code> made the path non-deterministic
                        if (!InstanceFieldEdge.fieldsAreDeterministic(newFields, originClassPath)) {
                            continue;
                        }
                        if (toReferences.contains(e.getValue())
                            && (atLeastOneStep || !fromReference.equals(toReference)))
                        {
                            annotations.add(new DefiniteReachabilityAnnotation(
                                fromReference,
                                toReference,
                                newFields,
                                atLeastOneStep,
                                originClassPath));
                        } else if (heapPositions.containsRef(e.getValue())) {
                            for (final StatePosition pos : heapPositions.getPositionsForRef(e.getValue())) {
                                if (!done.contains(pos)) {
                                    toAdd.put(pos, new Pair<>(newFields, true));
                                }
                            }
                        }
                    }
                }
                todo.putAll(toAdd);
                toAdd.clear();
            }
        }
        for (final DefiniteReachabilityAnnotation annotation : annotations) {
            assert (annotation.getFields().containsAll(fields));
            assert (atLeastOneStep || !annotation.isAtLeastOneStep());
        }
        return annotations;
    }

    /**
     * @param heapPositions {@code HeapPositions} of one of the merged state
     * @param annotationsForMergedState annotations that are valid in the other merged state
     * @param mergedHeapPositions {@code HeapPositions} of the merged state
     * @return Annotations for <code>mergedHeapPositions</code>, describing connections from <code>annotationsFromMergedState</code>
     *  that also exist in <code>heapPositions</code>. The fieldset of an annotation returned by this function might be a superset of
     *  the corresponding annotation from <code>annotationsFromMergedState</code>, as long as it is deterministic. The flag <code>atLeastOneStep</code>
     *  might not be set, even if it is set in the corresponding annotation from <code>annotationsFromMergedState</code>.
     */
    public static Set<DefiniteReachabilityAnnotation> filterDefiniteReachabilityAnnotations(
        final HeapPositions heapPositions,
        final Set<DefiniteReachabilityAnnotation> annotationsForMergedState,
        final HeapPositions mergedHeapPositions)
    {
        final Set<DefiniteReachabilityAnnotation> annotations = new LinkedHashSet<>();
        for (final DefiniteReachabilityAnnotation annotation : annotationsForMergedState) {
            annotations.addAll(DefiniteReachabilities.checkReachabilityExtendingFieldset(
                heapPositions,
                mergedHeapPositions,
                annotation.getFrom(),
                annotation.getTo(),
                annotation.isAtLeastOneStep(),
                annotation.getFields()));
        }
        return annotations;
    }


    public Collection<String> toSExpStrings() {
        final List<String> res = new LinkedList<>();
        for (final DefiniteReachabilityAnnotation dA : this.definiteReachabilities) {
            res.add(dA.toSExpString());
        }
        return res;
    }
}
