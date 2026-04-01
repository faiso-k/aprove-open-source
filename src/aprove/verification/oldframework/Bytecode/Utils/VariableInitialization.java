package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.runtime.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Class holding some useful methods for variable initialization.
 * @author Marc Brockschmidt
 */
public final class VariableInitialization {
    /**
     * Dummy constructor to prevent instantiation of this convenience class.
     */
    private VariableInitialization() {
        assert (false) : "Please do not try to instantiate this convenience class";
    }

    /**
     * Create a new abstract variable for a certain type signature, with
     * the JVMS default values, or with the most general possible values (in
     * cases in which they represent unknown input), or just null.
     * @param fuzzyType Type of the variable to create.
     * @param parentRef the reference of the ``parent'' of the new reference (or
     * null, if there is none)
     * @param state State in which the variable will live.
     * @param fieldValueSettings indicates what kind of value should be returned
     * @return {@link AbstractVariableReference} to the newly created (and
     * added) abstract variable
     */
    public static AbstractVariableReference getFreshVarFor(
        final FuzzyType fuzzyType,
        final AbstractVariableReference parentRef,
        final State state,
        final FieldValueSettings fieldValueSettings)
    {
        AbstractVariable newVar = null;
        AbstractVariableReference newRef = null;

        final ClassPath cPath = state.getClassPath();

        final AbstractType parentReachableTypes;
        if (parentRef != null) {
            parentReachableTypes = state.getHeapAnnotations().getReachableTypes(parentRef);
        } else {
            switch (fieldValueSettings) {
            case GENERAL_VALUE:
                parentReachableTypes =
                    new AbstractType(cPath, new FuzzyClassType(
                        FuzzyClassType.FT_JAVA_LANG_OBJECT.getMinimalClass(),
                        false));
                break;
            case DEFAULT_VALUE:
                parentReachableTypes = new AbstractType(cPath, FuzzyClassType.FT_JAVA_LANG_OBJECT);
                break;
            case NULL_VALUE:
                parentReachableTypes = null;
                break;
            default:
                assert (false);
                parentReachableTypes = null;
                break;
            }
        }

        if (fuzzyType.getArrayDimension() > 0) {
            switch (fieldValueSettings) {
            case GENERAL_VALUE:
                newRef =
                    new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);
                if (fuzzyType instanceof FuzzyClassType) {
                    final FuzzyClassType fct = (FuzzyClassType) fuzzyType;
                    final AbstractType declaredType = new AbstractType(cPath, fct.toAbstract());
                    final AbstractType newType;
                    if (parentReachableTypes != null) {
                        newType = AbstractType.intersection(cPath, state.getJBCOptions(), declaredType, parentReachableTypes);
                    } else {
                        newType = declaredType;
                    }
                    state.getHeapAnnotations().setAbstractType(newRef, newType);
                    state.getHeapAnnotations().setReachableTypes(newRef, parentReachableTypes);
                } else {
                    state.getHeapAnnotations().setAbstractType(newRef, new AbstractType(cPath, fuzzyType));
                    state.getHeapAnnotations().setReachableTypes(newRef, parentReachableTypes);
                }
                state.getHeapAnnotations().setMaybeExisting(newRef);
                break;
            case DEFAULT_VALUE:
                newVar = ObjectInstance.getDefaultValue();
                break;
            case NULL_VALUE:
                break;
            default:
                assert (false);
                break;
            }
        } else {
            switch (fuzzyType.getPrimitiveType()) {
            case BOOLEAN:
            case BYTE:
            case CHAR:
            case INTEGER:
            case SHORT:
                switch (fieldValueSettings) {
                case GENERAL_VALUE:
                    final IntegerType intType = IntegerType.UNBOUND;
                    newVar = AbstractInt.getUnknown(intType);
                    break;
                case DEFAULT_VALUE:
                    newVar = AbstractInt.getZero();
                    break;
                case NULL_VALUE:
                    break;
                default:
                    assert (false);
                    break;
                }
                break;
            case LONG:
                switch (fieldValueSettings) {
                case GENERAL_VALUE:
                    final IntegerType intType = IntegerType.UNBOUND;
                    newVar = AbstractInt.getUnknown(intType);
                    break;
                case DEFAULT_VALUE:
                    newVar = AbstractInt.getZero();
                    break;
                case NULL_VALUE:
                    break;
                default:
                    assert (false);
                    break;
                }
                break;
            case FLOAT:
                switch (fieldValueSettings) {
                case GENERAL_VALUE:
                    newVar = AbstractFloat.create();
                    break;
                case DEFAULT_VALUE:
                    newVar = AbstractFloat.getDefaultValue();
                    break;
                case NULL_VALUE:
                    break;
                default:
                    assert (false);
                    break;
                }
                break;
            case DOUBLE:
                switch (fieldValueSettings) {
                case GENERAL_VALUE:
                    newVar = AbstractFloat.create();
                    break;
                case DEFAULT_VALUE:
                    newVar = AbstractFloat.getDefaultValue();
                    break;
                case NULL_VALUE:
                    break;
                default:
                    assert (false);
                    break;
                }
                break;
            case ADDRESS:
                switch (fieldValueSettings) {
                case GENERAL_VALUE:
                    /*
                     * Create a new reference and give information about its
                     * type according to the field declaration.
                     */
                    newRef =
                        new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);

                    final FuzzyClassType sigType = (FuzzyClassType) fuzzyType;
                    IClass sigClass = cPath.getClass(sigType.getMinimalClass());
                    final AbstractType declaredType =
                        new AbstractType(cPath, new FuzzyClassType(sigType.getMinimalClass(), sigClass.isFinal(), sigType.getArrayDimension()));
                    final AbstractType newType;
                    if (parentReachableTypes != null) {
                        newType = AbstractType.intersection(cPath, state.getJBCOptions(), declaredType, parentReachableTypes);
                    } else {
                        newType = declaredType;
                    }

                    if (newType == null) {
                        // the reachable type information does not allow anything in this field but null
                        state.replaceReference(newRef, AbstractVariableReference.NULLREF);
                        newVar = ConcreteInstance.NULL;
                        newRef = null;
                    } else {
                        state.getHeapAnnotations().setAbstractType(newRef, newType);
                        state.getHeapAnnotations().setReachableTypes(newRef, parentReachableTypes);
                        state.getHeapAnnotations().setMaybeExisting(newRef);
                    }
                    break;
                case DEFAULT_VALUE:
                    newVar = ObjectInstance.getDefaultValue();
                    assert (newVar != null);
                    break;
                case NULL_VALUE:
                    break;
                default:
                    assert (false);
                    break;
                }
                break;
            default:
                if (Globals.DEBUG_MARC) {
                    System.err.println("WARNING: Couldn't create variable for type descriptor "
                        + fuzzyType.getTypeDescriptor());
                } else {
                    throw new NotYetImplementedException();
                }
            }
        }
        if (newRef == null && fieldValueSettings != FieldValueSettings.NULL_VALUE) {
            newRef = state.createReferenceAndAdd(newVar, fuzzyType.getPrimitiveType());
        }

        return newRef;
    }

    /**
     * Annotate abstract variable references <code>childRefs</code> as children
     * (aka directly reachable by a reference) of <code>parentRef
     * </code>. This entails marking them as possibly non-existing, adding
     * possible equalities and joins and noting possible cyclicity.
     * @param state State in which the variable will live.
     * @param parentRef Reference which is the parent of the new references.
     * @param childRefs References which are children of the old reference.
     * @param origState may be null. If non-null: the unmodified state where parentRef is not realized, yet
     * @param parentRefOrig the parentRef in origState (may be null if origState is null)
     * @return information about new definite reachability annotations
     */
    public static Collection<VariableInformation> annotateAsFreshChildRefs(
        final State state,
        final AbstractVariableReference parentRef,
        final Collection<Pair<HeapEdge, AbstractVariableReference>> childRefs,
        final State origState,
        final AbstractVariableReference parentRefOrig)
    {
        final HeapAnnotations annotations = state.getHeapAnnotations();
        final JoiningStructures joins = annotations.getJoiningStructures();
        final CyclicStructures cyclicRefs = annotations.getCyclicStructures();
        final EqualityGraph eqG = annotations.getEqualityGraph();
        final Collection<VariableInformation> res = new LinkedList<>();
        JBCOptions options = state.getJBCOptions();

        //Special case simple objects:
        final AbstractType parentType = annotations.getAbstractType(parentRef);
        final boolean parentHasOnlyOneField = state.getClassPath().typeHasOnlyOneRefField(parentType, options);

        boolean reachesDeterministicCycle = false;
        AbstractVariableReference cycleJoint = null;
        if (parentHasOnlyOneField) {
            //Find out if we have parent -!-> o -F!!-> o and o only has the field in F. Then, we can forget joining!
            outer: for (final DefiniteReachabilityAnnotation dra : annotations.getDefiniteReachabilities()) {
                if (dra.getFrom().equals(parentRef) && !dra.getTo().equals(parentRef)) {
                    //Find out if that child closes a cycle, i.e., is a cycle joint
                    final AbstractVariableReference childRef = dra.getTo();
                    for (final DefiniteReachabilityAnnotation dra2 : annotations.getDefiniteReachabilities()) {
                        if (dra2.getFrom().equals(childRef) && dra2.getTo().equals(childRef)) {
                            final ClassName minJointClass =
                                state.getAbstractType(childRef).getMinimalClass().getMinimalClass();
                            if (state.getClassPath().reachableTypesHaveOnlyOneRefField(minJointClass, options)) {
                                reachesDeterministicCycle = true;
                                cycleJoint = childRef;
                                break outer;
                            }
                        }
                    }
                }
            }
        }

        //We iterate over this while adding joins, so copy:
        final Collection<AbstractVariableReference> joinsWithParentRef =
            new LinkedHashSet<>(joins.getReferencesWithPartner(parentRef));

        final Collection<AbstractVariableReference> possiblySelfReachingChildren = new LinkedHashSet<>();

        /* Do the Joins-Annotations:
        *
        * Case 1: \exists parentRef -><- parentRef:
        *  + If parentRef allows cycles or is not fully realized, add childRef -><- parentRef:
        *     The new instance might reach parentRef again
        *  + Add childRef -><- childRef:
        *     childRef might be part of a non-tree structure
        *     that doesn't contain parentRef.
        */
        boolean parentSelfJoins = false;
        for (final AbstractVariableReference partner : joinsWithParentRef) {
            if (partner.equals(parentRef)) {
                parentSelfJoins = true;
                for (final Pair<HeapEdge, AbstractVariableReference> childRefPair : childRefs) {
                    final AbstractVariableReference childRef = childRefPair.y;
                    if (!childRef.pointsToReferenceType()) {
                        continue;
                    }
                    if (!(state.isFullyRealized(parentRef) && !cyclicRefs.isCyclic(parentRef))
                        && !reachesDeterministicCycle)
                    {
                        joins.add(childRef, parentRef);
                    }
                    joins.add(childRef, childRef);
                    possiblySelfReachingChildren.add(childRef);
                }
                break;
            }
        }

        final LinkedHashSet<Pair<HeapEdge, AbstractVariableReference>> checkEqualities = new LinkedHashSet<>();
        for (final Pair<HeapEdge, AbstractVariableReference> child : childRefs) {
            final HeapEdge childConnection = child.x;
            final AbstractVariableReference childRef = child.y;
            //If the child is primitive, we don't need this:
            if (!childRef.pointsToReferenceType() || childRef.isNULLRef()) {
                continue;
            }

            //Mark the child as possibly non-existing:
            annotations.setMaybeExisting(childRef);

            /* Case 2: parentRef -><- t, t != parentRef,
             *  + Add childRef -><- t
             *     The new instance might have successors that join t and t's successors might join childRef
             *  + Add childRef =?= t
             *     The new instance might *be* t
             */
            for (final AbstractVariableReference partner : joinsWithParentRef) {
                if (partner.equals(parentRef)) {
                    continue;
                }

                eqG.addPossibleEquality(state, childRef, partner);
                if (childRef.pointsToReferenceType()) {
                    joins.add(childRef, partner);
                }
            }

            // if going along the correct field, the new child definitely can reach what parent can reach
            final Set<DefiniteReachabilityAnnotation> newReachabilities = new LinkedHashSet<>();
            final Iterator<DefiniteReachabilityAnnotation> iterator =
                annotations.getDefiniteReachabilities().iterator();
            while (iterator.hasNext()) {
                final DefiniteReachabilityAnnotation reachability = iterator.next();
                if (reachability.getFrom().equals(parentRef)
                    && reachability.isAtLeastOneStep()
                    && reachability.getFields().contains(childConnection))
                {
                    final DefiniteReachabilityAnnotation newReachability =
                        new DefiniteReachabilityAnnotation(
                            childRef,
                            reachability.getTo(),
                            reachability.getFields(),
                            false,
                            state.getClassPath());
                    newReachabilities.add(newReachability);
                    res.add(new DefiniteReachabilityAnnotationCreation(
                        reachability,
                        newReachability,
                        IntegerRelationType.LT));

                    //childRef cannot be null because it did not reach partner yet
                    final ConcreteInstance oI = ConcreteInstance.newJLO(state);
                    state.removeAbstractVariable(childRef);
                    state.addAbstractVariable(childRef, oI);
                    annotations.setExistenceIsKnown(childRef);

                    // the used annotation can be removed
                    iterator.remove();
                }
            }
            annotations.getDefiniteReachabilities().addAll(newReachabilities);

            /*
             * Mark children as possibly non-tree:
             */
            if (childRef.pointsToReferenceType()) {
                if (annotations.isPossiblyNonTree(parentRef)) {
                    if (cyclicRefs.isCyclic(parentRef) || HeapAnnotations.canBeNonTree(childRef, state)) {
                        annotations.setPossiblyNonTree(childRef);
                    }
                }

                /*
                 * Handle cyclic structures. If the parent is marked as possibly
                 * cyclic, parentRef = childRef might hold. Even if not, childRef
                 * might be part of a cycle, so push the possibly cyclic annotation
                 * to the childRef.
                 */
                if (cyclicRefs.isCyclic(parentRef)) {
                    annotations.setPossiblyNonTree(childRef);
                    if (parentSelfJoins) {
                        checkEqualities.add(child);
                    }
                    annotations.setPossiblyCyclic(childRef, cyclicRefs.getNeededEdgesOf(parentRef));
                }

                final AbstractType childType = state.getAbstractType(childRef);

                /*
                 * If this could possibly be a an instance of java.lang.String, handle
                 * it accordingly.
                 */
                if (options.simplifiedStringHandling() && childType.containsStringType()) {
                    JLStringHelper.annotateFreshStringInstance(state, null, childRef);
                }
                if (options.simplifiedClassHandling() && childType.containsClassType()) {
                    JLClassHelper.annotateFreshClassInstance(state, null, childRef);
                }
            }
        }

        for (final Pair<HeapEdge, AbstractVariableReference> pair : checkEqualities) {
            // do not add parentRef =?= childRef if this leads to some impossible state
            boolean add = true;
            if (origState != null) {
                final HeapAnnotations origHeapAnnotations = origState.getHeapAnnotations();
                final EqualityGraph origEqGraph = origHeapAnnotations.getEqualityGraph();
                /*
                 * Is there some defreach annotation parentRef -{n}!-> z with parentRef != z and not parentRef =?= z?
                 * If so, with parentRef=childRef and parentRef.n=childRef we cannot reach z anymore. This is a
                 * conflict, so parentRef != childRef.
                 */
                for (final DefiniteReachabilityAnnotation defReach : origHeapAnnotations.getDefiniteReachabilities()) {
                    if (defReach.getFrom().equals(parentRefOrig)
                        && defReach.getFields().contains(pair.x)
                        && !parentRefOrig.equals(defReach.getTo()))
                    {
                        final AbstractVariableReference refTo = defReach.getTo();
                        if (!origEqGraph.areMarkedAsPossiblyEqual(parentRef, refTo)) {
                            /*
                             * parentRef.childConnection must lead to refTo, but instead it can loop if
                             * parentRef=childRef=parentRef.childConnection
                             */
                            add = false;
                            break;
                        }
                    }
                }
            }
            if (add) {
                eqG.addPossibleEquality(state, parentRef, pair.y);
            }
        }

        /*
         * For those children that might be part of a non-tree structure and
         * join each other, add the correct annotations:
         */

        if (annotations.isPossiblyNonTree(parentRef)) {
            for (final Pair<AbstractVariableReference, AbstractVariableReference> pair : Collection_Util
                .getPairs(possiblySelfReachingChildren))
            {
                final AbstractVariableReference childRef1 = pair.x;
                final AbstractVariableReference childRef2 = pair.y;
                eqG.addPossibleEquality(state, pair.x, pair.y);
                joins.add(childRef1, childRef2);
            }
        }

        if (parentHasOnlyOneField && reachesDeterministicCycle && cycleJoint != null) {
            joins.remove(parentRef, cycleJoint);
            cyclicRefs.remove(parentRef);
            annotations.getPossiblyNonTreeRefs().remove(parentRef);
        }

        return res;
    }

    /**
     * Fill the static fields of the given type with default values ("unknown").
     * @param state in which the field values need to be set.
     * @param pc the type that is being initialized
     */
    public static void fillStaticFieldsWithGeneralValues(final State state, final IClass pc) {
        final ClassName cn = pc.getClassName();
        for (final Map.Entry<String, Field> entry : pc.getStaticFields().entrySet()) {
            final String name = entry.getKey();
            final Field f = entry.getValue();
            final AbstractVariableReference oldRef = state.getStaticFields().get(cn, name);
            assert (oldRef == null) : "Trying to set value for "
                + cn.toString()
                + "."
                + name
                + ", although we already had some value.";
            final FuzzyType type = FuzzyType.parseTypeDescriptor(f.getDescriptor());
            final AbstractVariableReference newRef =
                VariableInitialization.getFreshVarFor(type, null, state, FieldValueSettings.GENERAL_VALUE);
            state.getStaticFields().set(cn, name, newRef);

            // add joins etc?
            annotateNewStaticField(state, newRef);
        }
    }

    /**
     * We just invented a static field for an already initialized class. We do not know the contents of this static
     * field, so it might make sense to allow cyclicity, add joins, ...
     * @param state the state were the static field was added
     * @param newRef the reference of the static field
     */
    private static void annotateNewStaticField(final State state, final AbstractVariableReference newRef) {
        if (!newRef.pointsToReferenceType()) {
            return;
        }
        final JBCOptions jbcOptions = state.getJBCOptions();
        final StaticFieldInitInfo staticFieldInitInfo = jbcOptions.staticFieldInitInfo;
        final HeapAnnotations ha = state.getHeapAnnotations();
        if (staticFieldInitInfo.annotateAsCyclic()) {
            ha.setPossiblyNonTree(newRef);
            ha.setPossiblyCyclic(newRef, Collections.<HeapEdge>emptySet());
            ha.getJoiningStructures().add(newRef, newRef);
        } else if (staticFieldInitInfo.annotateAsNonTree()) {
            ha.setPossiblyNonTree(newRef);
            ha.getJoiningStructures().add(newRef, newRef);
        }

        Collection<AbstractVariableReference> refs;
        if (staticFieldInitInfo.sharesWithEverything()) {
            refs = state.getReferences().keySet();
        } else if (staticFieldInitInfo.sharesWithStaticFields()) {
            refs = state.getStaticFields().getValues();
        } else {
            refs = Collections.emptySet();
        }

        final JoiningStructures joins = ha.getJoiningStructures();
        final EqualityGraph eqGraph = ha.getEqualityGraph();
        for (final AbstractVariableReference ref : refs) {
            if (ref.isNULLRef() || !ref.pointsToReferenceType() || ref.equals(newRef)) {
                continue;
            }

            joins.add(ref, newRef);
            eqGraph.addPossibleEquality(state, ref, newRef);
        }
    }

    /**
     * For each field with a ConstantValue attribute, fill in the corresponding
     * value.
     * @param state in which the field values need to be set.
     * @param parsedClass the type that is being initialized
     */
    public static void fillStaticFieldsWithConstantValues(final State state, final IClass parsedClass) {
        for (final Map.Entry<String, Field> entry : parsedClass.getStaticFields().entrySet()) {
            final Field field = entry.getValue();

            // do we know a ConstantValue attribute for the field?
            final Object constantValue = field.getConstantValue();
            if (constantValue != null) {
                AbstractVariableReference newRef;
                if (constantValue instanceof Integer) {
                    final AbstractInt newInt = AbstractInt.create((Integer) constantValue);
                    newRef = state.createReferenceAndAdd(newInt, OperandType.INTEGER);
                } else if (constantValue instanceof Long) {
                    final AbstractInt newInt = AbstractInt.create((Long) constantValue);
                    newRef = state.createReferenceAndAdd(newInt, OperandType.LONG);
                } else if (constantValue instanceof Float) {
                    final AbstractFloat newFloat = AbstractFloat.create((Float) constantValue);
                    newRef = state.createReferenceAndAdd(newFloat, OperandType.FLOAT);
                } else if (constantValue instanceof Double) {
                    final AbstractFloat newFloat = AbstractFloat.create((Double) constantValue);
                    newRef = state.createReferenceAndAdd(newFloat, OperandType.DOUBLE);
                } else if (constantValue instanceof String) {
                    newRef = JLStringHelper.addConstantStringToStateOrThrow(state, (String) constantValue);
                } else {
                    assert (false) : "Unknown instance for static default value: " + constantValue;
                    newRef = null;
                }

                state.getStaticFields().set(field.getClassName(), field.getName(), newRef);
            }
        }
    }

    /**
     * Fill the static fields of the given type with 0/null.
     * @param state in which the field values need to be set.
     * @param parsedClass the type that is being initialized
     */
    public static void fillStaticFieldsWithDefaultValues(final State state, final IClass parsedClass) {
        final ClassName cn = parsedClass.getClassName();
        for (final Map.Entry<String, Field> entry : parsedClass.getStaticFields().entrySet()) {
            final String fieldName = entry.getKey();
            final Field field = entry.getValue();
            final AbstractVariableReference oldRef = state.getStaticFields().get(cn, fieldName);
            assert (oldRef == null) : "Trying to set value for "
                + cn.toString()
                + "."
                + fieldName
                + ", although we already had some value.";
            final AbstractVariableReference newRef;

            // set to 0/null
            final FuzzyType type = FuzzyType.parseTypeDescriptor(field.getDescriptor());
            newRef = VariableInitialization.getFreshVarFor(type, null, state, FieldValueSettings.DEFAULT_VALUE);
            state.getStaticFields().set(cn, fieldName, newRef);
        }
    }
}
