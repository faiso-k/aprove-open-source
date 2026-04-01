/**
 * @author marc
 */
package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This object encapsulates all annotations we have that describe the heap.
 */
public class HeapAnnotations implements Cloneable {
    /**
     * Maps instances to type information about them - even if we haven't
     * created the instance yet, we might know that it is at least implementing
     * some class (or even know that it won't be more specialized).
     */
    private Map<AbstractVariableReference, AbstractType> abstractTypes;

    /**
     * Maps a reference to a (super)set of all types reachable from it. Only
     * contains reference types, ignores primitive types.
     */
    private Map<AbstractVariableReference, AbstractType> reachableTypes;

    /**
     * Implementation of the a@{field1 field2} ("a is cyclic using field1 and
     * field2") annotation.
     */
    private CyclicStructures cyclicStructures;

    /**
     * Undirected graph of possibly equal objects (wherever two objects might be
     * equal, we add an edge).
     */
    private EqualityGraph equalityGraph;

    /**
     * Implementation of the a -><- b annotation ("a joins b").
     */
    private JoiningStructures joiningStructures;

    /**
     * Set of instances of which we don't know yet if they are existing - when
     * working on them, we will refine and get two cases: Either we know it
     * exists, or it does not exist and we can replace the reference by the
     * special null reference. In both cases we can remove the reference from
     * this set.
     */
    private Set<AbstractVariableReference> maybeExistingInstances;

    /**
     * Set of AbstractVariableReferences that point to reference types that may
     * have a non-tree shape.
     */
    private Set<AbstractVariableReference> nonTreeReferences;

    /**
     * The known definite reachability information.
     */
    private DefiniteReachabilities definiteReachabilities;

    /**
     * More information about abstract arrays.
     */
    private ArrayInfo arrayInfo;

    /**
     * Initialize the data without any useful content.
     */
    public HeapAnnotations() {
        this.abstractTypes = new LinkedHashMap<>();
        this.reachableTypes = new LinkedHashMap<>();
        this.maybeExistingInstances = new LinkedHashSet<>();
        this.equalityGraph = new EqualityGraph();
        this.joiningStructures = new JoiningStructures();
        this.cyclicStructures = new CyclicStructures();
        this.nonTreeReferences = new LinkedHashSet<>();
        this.definiteReachabilities = new DefiniteReachabilities();
        this.arrayInfo = new ArrayInfo();
    }

    /**
     * Fill this annotations object with all annotations for some ref found in another state's annotations.
     * @param state the state to which annotations are added.
     * @param otherAnnotations the annotations object to copy from
     * @param ref the reference for which annotations should be copied.
     */
    public void addAllDataFrom(
        final State state,
        final HeapAnnotations otherAnnotations,
        final AbstractVariableReference ref)
    {
        final AbstractType type = otherAnnotations.getAbstractType(ref);
        if (type != null) {
            this.setAbstractType(ref, type);
        }
        final AbstractType otherReachableTypes = otherAnnotations.getReachableTypes(ref);
        this.setReachableTypes(ref, otherReachableTypes);
        if (otherAnnotations.isPossiblyNonTree(ref)) {
            this.setPossiblyNonTree(ref);
        }
        final CyclicStructures otherCyclic = otherAnnotations.getCyclicStructures();
        if (otherCyclic.isCyclic(ref)) {
            this.cyclicStructures.add(ref, otherCyclic.getNeededEdgesOf(ref));
        }
        for (final AbstractVariableReference partner : otherAnnotations.equalityGraph.getPartners(ref)) {
            this.equalityGraph.addPossibleEquality(state, ref, partner);
        }
        final JoiningStructures otherJoins = otherAnnotations.getJoiningStructures();
        for (final AbstractVariableReference partner : otherJoins.getReferencesWithPartner(ref)) {
            this.joiningStructures.add(partner, ref);
        }
        this.definiteReachabilities.addAll(otherAnnotations.getDefiniteReachabilities().getDefReachesByStartRef(ref));
        this.definiteReachabilities.addAll(otherAnnotations.getDefiniteReachabilities().getDefReachesByTargetRef(ref));
        if (otherAnnotations.isMaybeExisting(ref)) {
            this.setMaybeExisting(ref);
        }
        this.arrayInfo.addAllDataFrom(otherAnnotations.arrayInfo, ref);
    }

    /**
     * Copy the unary annotations (type, existence, non-tree, cyclic) for ref to
     * newRef in toState.
     * @param ref a reference
     * @param toState copy information into this state
     * @param newRef the reference for which the information should be added
     */
    public void copyUnaryAnnotationsToState(
        final AbstractVariableReference ref,
        final State toState,
        final AbstractVariableReference newRef)
    {
        final AbstractType abstractType = this.getAbstractType(ref);
        toState.getHeapAnnotations().setAbstractType(newRef, abstractType);
        final AbstractType reachableT = this.getReachableTypes(ref);
        toState.getHeapAnnotations().setReachableTypes(newRef, reachableT);
        if (this.isMaybeExisting(ref)) {
            toState.getHeapAnnotations().setMaybeExisting(newRef);
        }
        if (this.isPossiblyNonTree(ref)) {
            toState.getHeapAnnotations().setPossiblyNonTree(newRef);
        }
        if (this.getCyclicStructures().isCyclic(ref)) {
            toState.getHeapAnnotations().setPossiblyCyclic(newRef, this.getCyclicStructures().getNeededEdgesOf(ref));
        }
    }

    /**
     * Returns a deep (!) copy of this {@link HeapAnnotations} object.
     * @return Deep copy of this object
     */
    @Override
    public HeapAnnotations clone() {
        final HeapAnnotations clone = new HeapAnnotations();

        clone.equalityGraph = this.equalityGraph.clone();

        clone.joiningStructures = this.joiningStructures.clone();

        clone.cyclicStructures = this.cyclicStructures.clone();

        clone.nonTreeReferences = new LinkedHashSet<>(this.nonTreeReferences);

        clone.maybeExistingInstances = new LinkedHashSet<>(this.maybeExistingInstances);

        clone.abstractTypes = new LinkedHashMap<>();
        for (final Map.Entry<AbstractVariableReference, AbstractType> e : this.abstractTypes.entrySet()) {
            clone.abstractTypes.put(e.getKey(), e.getValue());
        }

        clone.reachableTypes = new LinkedHashMap<>();
        for (final Map.Entry<AbstractVariableReference, AbstractType> e : this.reachableTypes.entrySet()) {
            clone.reachableTypes.put(e.getKey(), e.getValue());
        }

        clone.definiteReachabilities = this.definiteReachabilities.clone();

        clone.arrayInfo = this.arrayInfo.clone();

        return clone;
    }

    /**
     * This removes every information from the state that is not "reachable"
     * from the stack or any static field.
     * @param s the enclosing state
     * @param refsToKeep references that are supposed to be kept.
     * @param refsToRemove references that are removed from the state [set may be extended!]
     * @return true if any annotation was removed (e.g. because we inferred it
     * is not possible).
     */
    public Pair<Boolean, Set<VariableInformation>> gc(
        final State s,
        final Collection<AbstractVariableReference> refsToKeep,
        final Collection<AbstractVariableReference> refsToRemove)
    {
        for (final AbstractVariableReference id : this.abstractTypes.keySet()) {
            if (!refsToKeep.contains(id)) {
                refsToRemove.add(id);
            }
        }
        for (final AbstractVariableReference id : refsToRemove) {
            this.justRemove(id);
        }

        boolean annotationRemoved = this.equalityGraph.clean(s);
        annotationRemoved = this.joiningStructures.clean(s);
        annotationRemoved |= this.arrayInfo.clean(refsToRemove, s);

        if (Globals.DEBUG_MARC) {
            for (final AbstractVariableReference ref : refsToKeep) {
                if (ref.isNULLRef() || !ref.pointsToReferenceType()) {
                    continue;
                }
                assert (this.reachableTypes.get(ref) != null) : "No reachable types for object ref " + ref;
            }
        }

        final Pair<Boolean, Set<VariableInformation>> pair = DefiniteReachabilities.gc(s, refsToRemove);
        if (pair.x) {
            annotationRemoved = true;
        }
        final Set<VariableInformation> annotationChanges = pair.y;

        return new Pair<>(annotationRemoved, annotationChanges);
    }

    /**
     * @param ref {@link AbstractVariableReference} to return type information
     * for.
     * @return type information about var
     */
    public AbstractType getAbstractType(final AbstractVariableReference ref) {
        return this.abstractTypes.get(ref);
    }

    /**
     * @param ref {@link AbstractVariableReference} to return reachable type information
     * for.
     * @return reachable types for <code>ref</code>
     */
    public AbstractType getReachableTypes(final AbstractVariableReference ref) {
        final AbstractType res = this.reachableTypes.get(ref);
        if (ref.pointsToReferenceType()) {
            assert (res != null);
        }
        return res;
    }

    /**
     * @return our representation of the "cyclic" annotations
     */
    public CyclicStructures getCyclicStructures() {
        return this.cyclicStructures;
    }

    /**
     * @return our representation of the "equals" annotations
     */
    public EqualityGraph getEqualityGraph() {
        return this.equalityGraph;
    }

    /**
     * @return our representation of the "joins" annotations
     */
    public JoiningStructures getJoiningStructures() {
        return this.joiningStructures;
    }

    /**
     * Do not modify!
     * @return all references to instances that are marked as maybe existing
     */
    public Set<AbstractVariableReference> getMaybeExistingInstances() {
        return this.maybeExistingInstances;
    }

    /**
     * @return our set of references objects that may have a non-tree shape.
     */
    public Set<AbstractVariableReference> getPossiblyNonTreeRefs() {
        return this.nonTreeReferences;
    }

    /**
     * @return all known definit reaches annotations.
     */
    public DefiniteReachabilities getDefiniteReachabilities() {
        return this.definiteReachabilities;
    }

    /**
     * @param ref {@link AbstractVariableReference} which either points to
     * nothing or an already instantiated {@link ConcreteInstance}.
     * @return true iff the referenced {@link ConcreteInstance} might exist (i. e., we do not know that it is null and
     * we do not know that it references an existing instance)
     */
    public boolean isMaybeExisting(final AbstractVariableReference ref) {
        return this.maybeExistingInstances.contains(ref);
    }

    /**
     * @param r Some {@link AbstractVariableReference}
     * @return true if r may have a non-tree shape on the heap.
     */
    public boolean isPossiblyNonTree(final AbstractVariableReference r) {
        return this.nonTreeReferences.contains(r);
    }

    /**
     * Replace one reference by another. Take care that the abstract type
     * information of the old references is also copied to the new reference!
     *
     * @param s the enclosing state
     * @param oldRef the reference to be replaced
     * @param newRef the new reference
     */
    public void replaceReference(
        final State s,
        final AbstractVariableReference oldRef,
        final AbstractVariableReference newRef)
    {
        //Also carry over all annotations for instances:
        this.equalityGraph.replaceReference(oldRef, newRef);

        this.arrayInfo.replaceReference(oldRef, newRef);

        if (this.maybeExistingInstances.contains(oldRef)) {
            this.maybeExistingInstances.remove(oldRef);
            if (!newRef.isNULLRef()) {
                this.maybeExistingInstances.add(newRef);
            }
        }

        if (!newRef.isNULLRef()) {
            assert (!oldRef.isNULLRef());
            final AbstractType oldType = this.abstractTypes.get(oldRef);
            if (oldType != null) {
                this.setAbstractType(newRef, oldType);
            }

            final AbstractType oldReachableTypes = this.reachableTypes.get(oldRef);
            if (oldReachableTypes != null) {
                this.setReachableTypes(newRef, oldReachableTypes);
            }

        }
        this.abstractTypes.remove(oldRef);
        this.reachableTypes.remove(oldRef);

        this.joiningStructures.replace(oldRef, newRef);

        this.cyclicStructures.replace(oldRef, newRef);

        final Collection<AbstractVariableReference> oldNonTreeRefs = new LinkedHashSet<>(this.nonTreeReferences);
        this.nonTreeReferences.clear();
        for (final AbstractVariableReference ref : oldNonTreeRefs) {
            if (ref.equals(oldRef)) {
                if (!newRef.isNULLRef()) {
                    this.nonTreeReferences.add(newRef);
                }
            } else {
                this.nonTreeReferences.add(ref);
            }
        }

        this.definiteReachabilities.replaceReference(s, oldRef, newRef);
    }

    /**
     * Record that variable points to an instance which is of the given abstract
     * type.
     * @param ref {@link AbstractVariableReference} to record the class of.
     * @param type of the variable referenced by ref.
     */
    public void setAbstractType(final AbstractVariableReference ref, final AbstractType type) {
        this.abstractTypes.put(ref, type);
    }

    /**
     * Record that a reference can reach a certain set of types
     * @param ref some {@link AbstractVariableReference}
     * @param type abstract type describing all reachable types
     */
    public void setReachableTypes(final AbstractVariableReference ref, final AbstractType type) {
        if (ref.pointsToReferenceType()) {
            assert (type != null) : "Cannot have NULL as reachable types";
            this.reachableTypes.put(ref, type);
        }
    }

    /**
     * Record that a reference additionally can reach a certain set of types.
     * @param ref some {@link AbstractVariableReference}
     * @param additionalType abstract type describing more reachable types
     * @param cPath the considered class path for this analysis.
     */
    public void addReachableTypes(
        final AbstractVariableReference ref,
        final AbstractType additionalType,
        final ClassPath cPath,
        final JBCOptions options)
    {
        this.addReachableTypes(ref, Collections.singleton(additionalType), cPath, options);
    }

    /**
     * Record that a reference additionally can reach a certain set of types.
     * @param ref some {@link AbstractVariableReference}
     * @param additionalTypes abstract types describing more reachable types
     * @param cPath the considered class path for this analysis.
     */
    public void addReachableTypes(
        final AbstractVariableReference ref,
        final Collection<AbstractType> additionalTypes,
        final ClassPath cPath,
        final JBCOptions options)
    {
        assert (!additionalTypes.isEmpty());
        if (this.reachableTypes.containsKey(ref)) {
            final AbstractType oldType = this.reachableTypes.get(ref);
            final Collection<AbstractType> newCollection = new LinkedHashSet<>(additionalTypes);
            newCollection.add(oldType);
            final AbstractType newType = AbstractType.union(cPath, options, newCollection);
            this.reachableTypes.put(ref, newType);
        } else {
            final AbstractType union = AbstractType.union(cPath, options, additionalTypes);
            this.reachableTypes.put(ref, union);
        }
    }

    /**
     * Denote that we know about the existance status of the referenced instance
     * (remove it from "may exist").
     * @param varRef a reference
     * @return true iff the reference was marked as maybe-existing before
     */
    public boolean setExistenceIsKnown(final AbstractVariableReference varRef) {
        return this.maybeExistingInstances.remove(varRef);
    }

    /**
     * Remember that the reference is of tree shape.
     * @param ref some reference
     */
    public void setIsTree(final AbstractVariableReference ref) {
        this.nonTreeReferences.remove(ref);
        this.cyclicStructures.remove(ref);
    }

    /**
     * Records that the referenced variable may exist.
     * @param ref {@link AbstractVariableReference} which points to nothing
     */
    public void setMaybeExisting(final AbstractVariableReference ref) {
        assert (!ref.isNULLRef());
        this.maybeExistingInstances.add(ref);
    }

    /**
     * Note a@.
     * @param ref Guess from the description.
     * @param neededEdges heap edges that must exist on any cycle involving ref.
     * @return true iff this was a new cyclic annotation (also true if the set
     * of needed edges got smaller)
     */
    public boolean setPossiblyCyclic(final AbstractVariableReference ref, final Collection<HeapEdge> neededEdges) {
        assert (!neededEdges.contains(UnknownArrayMemberEdge.INSTANCE));
        assert (this.nonTreeReferences.contains(ref));
        return this.cyclicStructures.add(ref, neededEdges);
    }

    /**
     * Mark that a variable reference is allowed to point to a data structure
     * which might not be a tree.
     * @param r Some {@link AbstractVariableReference}
     * @return true iff the reference was added
     */
    public boolean setPossiblyNonTree(final AbstractVariableReference r) {
        return this.nonTreeReferences.add(r);
    }

    /**
     * This method is used when merging two NRIRs into one. To be correct, the
     * annotations must be merged. to do this, we copy the "bad" annotations
     * from replaced to replacement and "remove" the good annotations (DefReach)
     * in the other direction.
     * @param state the state for which we change the annotations
     * @param replaced the reference which will be removed
     * @param replacement the reference which will remain
     */
    public void mergeAnnotationsForNRIRMerge(
        final State state,
        final AbstractVariableReference replaced,
        final AbstractVariableReference replacement)
    {
        final AbstractVariable replacedVar = state.getAbstractVariable(replaced);
        assert (replacedVar == null || replacedVar instanceof ObjectInstance);
        if (replacedVar instanceof ConcreteInstance) {
            assert (((ConcreteInstance) replacedVar).isOnlyRealizedUpToJLO());
        }

        final AbstractVariable replacementVar = state.getAbstractVariable(replacement);
        assert (replacementVar == null || replacementVar instanceof ObjectInstance);
        if (replacementVar instanceof ConcreteInstance) {
            assert (((ConcreteInstance) replacementVar).isOnlyRealizedUpToJLO());
        }

        final AbstractType typeReplaced = this.abstractTypes.get(replaced);
        final AbstractType typeReplacement = this.abstractTypes.get(replacement);
        final AbstractType mergedType;
        if (typeReplacement == null) {
            mergedType = typeReplaced;
        } else {
            mergedType = AbstractType.union(state.getClassPath(), state.getJBCOptions(), typeReplaced, typeReplacement);
        }
        this.abstractTypes.put(replacement, mergedType);

        final AbstractType reachableReplaced = this.reachableTypes.get(replaced);
        final AbstractType mergedReachable;
        final AbstractType reachableReplacement = this.reachableTypes.get(replacement);
        if (reachableReplacement == null) {
            mergedReachable = reachableReplaced;
        } else {
            mergedReachable = AbstractType.union(state.getClassPath(), state.getJBCOptions(), reachableReplaced, reachableReplacement);
        }

        this.reachableTypes.put(replacement, mergedReachable);

        if (this.maybeExistingInstances.contains(replaced)) {
            this.maybeExistingInstances.add(replacement);
        }
        if (this.nonTreeReferences.contains(replaced)) {
            this.nonTreeReferences.add(replacement);
        }
        if (this.cyclicStructures.isCyclic(replaced)) {
            this.cyclicStructures.add(replacement, this.cyclicStructures.getNeededEdgesOf(replaced));
        }

        for (final AbstractVariableReference other : this.equalityGraph.getPartners(replaced)) {
            this.equalityGraph.addPossibleEquality(state, replacement, other);
            if (other.equals(replaced)) {
                this.equalityGraph.addPossibleEquality(state, replacement, replacement);
            }
        }
        final Collection<Pair<AbstractVariableReference, AbstractVariableReference>> addMe = new LinkedHashSet<>();
        for (final AbstractVariableReference partner : this.joiningStructures.getReferencesWithPartner(replaced)) {
            addMe.add(new Pair<>(replacement, partner));
            if (partner.equals(replaced)) {
                addMe.add(new Pair<>(replacement, replacement));
            }
        }
        for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : addMe) {
            this.joiningStructures.add(pair.x, pair.y);
        }

        final Set<AbstractVariableReference> refsToRemove = new LinkedHashSet<>();
        refsToRemove.add(replaced);
        refsToRemove.add(replacement);
        this.arrayInfo.clean(refsToRemove, state);

        // TODO retain some DefReach
        this.definiteReachabilities.removeAnnotationsContainingReferences(replaced, replacement);
    }

    /**
     * Attention: Only trust the result if you ensured that ref is acyclic!
     * @param ref a reference
     * @param state a state with ref
     * @return false only if we ensured that ref cannot lead to a acyclic
     * non-tree shape, e.g. because ref only has at most one reference field.
     */
    public static boolean canBeNonTree(final AbstractVariableReference ref, final State state) {
        if (state.getHeapAnnotations().isPossiblyNonTree(ref)) {
            return true;
        }
        assert (ref.pointsToReferenceType());
        final AbstractVariable var = state.getAbstractVariable(ref);
        if (var instanceof ConcreteArray) {
            final ConcreteArray array = (ConcreteArray) var;
            if (array.getLiteralLength() == 0) {
                return false;
            }
        }

        final LinkedList<Pair<ClassName, Boolean>> toCheck = new LinkedList<>();

        final AbstractType type = state.getAbstractType(ref);
        for (final FuzzyType ft : type.getPossibleClassesCopy()) {
            if (ft.isArrayType()) {
                if (ft.getEnclosedType() instanceof FuzzyClassType) {
                    // Object[] x = new Object[]{a, a};
                    return true;
                }
            } else {
                assert (ft instanceof FuzzyClassType);
                final FuzzyClassType fct = (FuzzyClassType) ft;
                final ClassName cn = fct.getMinimalClass();
                toCheck.add(new Pair<>(cn, fct.isAbstract()));
            }
        }
        final Collection<ClassName> checked = new LinkedHashSet<>();
        while (!toCheck.isEmpty()) {
            final Pair<ClassName, Boolean> pair = toCheck.pop();
            final ClassName cn = pair.x;
            final boolean expand = pair.y;

            if (expand) {
                if (cn.equals(ClassName.Important.JAVA_LANG_OBJECT.getClassName())) {
                    // every array is instance of Object
                    return true;
                }
                if (cn.equals(ClassName.Important.JAVA_IO_SERIALIZABLE.getClassName())) {
                    // every array is instance of Serializable
                    return true;
                }
                if (cn.equals(ClassName.Important.JAVA_LANG_CLONEABLE.getClassName())) {
                    // every array is instance of Cloneable
                    return true;
                }

                final TypeTree typeTree = state.getClassPath().getTypeTree(cn);
                for (final TypeTree subType : typeTree.expand(state.getJBCOptions())) {
                    if (subType.equals(typeTree)) {
                        continue;
                    }
                    toCheck.add(new Pair<>(subType.getClassName(), Boolean.TRUE));
                }
            }

            if (!checked.add(cn)) {
                continue;
            }

            final IClass cls = state.getClassPath().getClass(cn);
            boolean hasReferenceField = false;
            for (final Field field : cls.getInstanceFields().values()) {
                final FuzzyType fuzzyType = FuzzyType.parseTypeDescriptor(field.getDescriptor());
                if (fuzzyType instanceof FuzzyClassType) {
                    if (hasReferenceField) {
                        return true;
                    }
                    hasReferenceField = true;
                    final ClassName fieldClassName = ((FuzzyClassType) fuzzyType).getMinimalClass();
                    toCheck.add(new Pair<>(fieldClassName, Boolean.TRUE));
                } else if (fuzzyType.isArrayType()) {
                    if (fuzzyType.getEnclosedType() instanceof FuzzyClassType) {
                        // Object[] x = new Object[]{a, a};
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * Remove everything we know about the reference
     * @param ref a reference
     */
    public void justRemove(final AbstractVariableReference ref) {
        this.abstractTypes.remove(ref);
        this.reachableTypes.remove(ref);
        this.maybeExistingInstances.remove(ref);
        this.joiningStructures.remove(ref);
        this.cyclicStructures.remove(ref);
        this.nonTreeReferences.remove(ref);
        this.equalityGraph.remove(ref);
        this.arrayInfo.remove(ref);
    }

    /**
     * @return all references that somehow appear in the annotations
     */
    public Collection<? extends AbstractVariableReference> getReferences() {
        final Collection<AbstractVariableReference> res = new LinkedHashSet<>();
        res.addAll(this.maybeExistingInstances);
        res.addAll(this.nonTreeReferences);
        res.addAll(this.abstractTypes.keySet());
        res.addAll(this.cyclicStructures.getCyclicRefs());
        res.addAll(this.definiteReachabilities.getReferences());
        res.remove(null);
        res.addAll(this.equalityGraph.getReferences());
        res.addAll(this.joiningStructures.getReferences());
        res.addAll(this.reachableTypes.keySet());
        res.addAll(this.arrayInfo.getReferences());
        return res;
    }

    /**
     * @return information about abstract arrays
     */
    public ArrayInfo getArrayInfo() {
        return this.arrayInfo;
    }

    /**
     * remove all annotations
     */
    public void clear() {
        this.getMaybeExistingInstances().clear();
        this.nonTreeReferences.clear();
        this.getCyclicStructures().clear();
        this.getEqualityGraph().clear();
        this.getJoiningStructures().clear();
        this.getDefiniteReachabilities().clear();
        this.getArrayInfo().clear();
    }

    public JSONArray toJSON() throws JSONException {
        final JSONArray res = new JSONArray();

        //TODO (maybe): abstractTypes, reachableTypes, arrayInfo

        for (final AbstractVariableReference ref : this.maybeExistingInstances) {
            res.put("(maybe-existing " + ref.toString() + ")");
        }

        for (final String joinStr : this.joiningStructures.toSExpStrings()) {
            res.put(joinStr);
        }

        for (final String eqStr : this.equalityGraph.toSExpStrings()) {
            res.put(eqStr);
        }

        for (final String cStr : this.cyclicStructures.toSExpStrings()) {
            res.put(cStr);
        }

        for (final String dStr : this.definiteReachabilities.toSExpStrings()) {
            res.put(dStr);
        }

        for (final AbstractVariableReference ref : this.nonTreeReferences) {
            res.put("(maybe-nontree " + ref.toString() + ")");
        }

        return res;
    }
}
