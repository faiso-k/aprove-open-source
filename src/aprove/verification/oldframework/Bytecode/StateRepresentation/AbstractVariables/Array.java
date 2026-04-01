package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.util.*;

import org.json.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Parent class of the different array representations supported by AProVE.
 *
 * @author Marc Brockschmidt
 */
public abstract class Array extends AbstractVariable {
    /**
     * Length of this array.
     */
    private AbstractVariableReference lengthRef;

    /**
     * Create an array with the length defined by the given reference
     * @param length a reference to this array's length
     */
    public Array(final AbstractVariableReference length) {
        this.lengthRef = length;
    }

    /**
     * Returns a deep (!) copy of this {@link AbstractArray} object
     * @return Deep copy of this object
     */
    @Override
    public Array clone() {
        final Array clone = (Array) super.clone();
        this.lengthRef = this.lengthRef.clone();
        return clone;
    }

    /**
     * @param myRef reference to the current variable
     * @param varUsers a map giving information about the number of places the
     * given reference is used.
     * @param state current state
     * @param shortRepresentation if some value only occurs at a single
     * position, show the value instead of the reference
     * @return String representation of this {@link Array}.
     */
    public abstract String toString(final AbstractVariableReference myRef,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        boolean shortRepresentation);

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.toString(null, null, null, true);
    }

    /**
     * @return false, because we already know this is an existing array.
     */
    @Override
    public final boolean isNULL() {
        return false;
    }

    /**
     * @return reference to the AbstractInt representing this array's length
     */
    public AbstractVariableReference getLength() {
        return this.lengthRef;
    }

    /**
     * @return a map from used abstract variable references to the number of
     * uses of them in this array.
     */
    public abstract Map<AbstractVariableReference, Integer> getReferences();

    /**
     * Replace <code>oldRef</code> with <code>newRef</code>.
     *
     * @param oldRef old abstract variable reference
     * @param newRef new abstract variable reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        if (this.lengthRef.equals(oldRef)) {
            this.lengthRef = newRef;
        }
    }

    /**
     * Get a value from an array in a certain index range.
     *
     * A single variable reference is returned, and all other references that may
     * point to the same cell in the array are marked as possibly equal.
     *
     * @param state state in which this array is used (needed for variable lookups, equality marking)
     * @param arrayRef {@link AbstractVariableReference} to this array (needed for type lookups)
     * @param indexRef index of the stored element
     * @return an {@link AbstractVariableReference} to a fitting abstract variable, either freshly
     *  created or re-used from former accesses of this array.
     */
    public abstract AbstractVariableReference load(final State state,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef);

    /**
     * Note that a value was put into this array at a certain index.
     * @param state state in which this array is used (needed for variable
     * lookups)
     * @param arrayRef reference to this array
     * @param indexRef index of the stored element
     * @param isPrimitive true iff this array contains primitive values
     * @param valueRef reference to the stored element
     * @return information about changes in Defreach annotations that _must_ be regarded
     */
    public abstract Collection<DefiniteReachabilityAnnotationCreation> store(final State state,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef,
        final AbstractVariableReference valueRef,
        final boolean isPrimitive);

    /**
     * Load an unknown variable from an array.
     *
     * @param state state in which this array is used (needed for variable
     * lookups)
     * @param arrayRef reference to this array
     * @return fresh {@link AbstractVariableReference}, annotated correctly
     *  as child of <code>arrayRef</code> according to the existing annotations
     *  in <code>state</code>
     */
    protected static AbstractVariableReference loadFreshVar(final State state, final AbstractVariableReference arrayRef) {
        AbstractVariableReference resVarRef;

        //Get type for the array:
        final AbstractType arrayT = state.getAbstractType(arrayRef);
        final AbstractType enclosedType = arrayT.getEnclosedTypes(state.getClassPath(), state.getJBCOptions());

        //Create a new value:
        final boolean hasPrimitive = enclosedType.containsPrimitiveType();

        if (hasPrimitive) {
            assert (enclosedType.isConcrete()) : "ERROR: Variable must be a known primitive type.";
            final FuzzyType t = enclosedType.getPrimitiveType();
            resVarRef = VariableInitialization.getFreshVarFor(t, arrayRef, state, FieldValueSettings.GENERAL_VALUE);
        } else {
            resVarRef = new AbstractVariableReference(UIDGenerator.getObjectUIDGenerator().next(), OperandType.ADDRESS);

            final ClassPath cPath = state.getClassPath();
            final AbstractType parentReachableTypes = state.getHeapAnnotations().getReachableTypes(arrayRef);

            /*
             * The array declaration gives a concrete type X, but the contained
             * instance can have any subtype of X.
             */
            final AbstractType nonConcreteTypes = enclosedType.getNonConcreteTypes(cPath, state.getJBCOptions());

            final AbstractType newType = AbstractType.intersection(cPath, state.getJBCOptions(), parentReachableTypes, nonConcreteTypes);

            if (newType == null) {
                resVarRef = AbstractVariableReference.NULLREF;
            } else {
                state.getHeapAnnotations().setAbstractType(resVarRef, newType);
                state.getHeapAnnotations().setReachableTypes(resVarRef, parentReachableTypes);
            }

            VariableInitialization.annotateAsFreshChildRefs(state, arrayRef,
                Collections.singleton(new Pair<HeapEdge, AbstractVariableReference>(UnknownArrayMemberEdge.INSTANCE,
                    resVarRef)), null, null);
        }

        return resVarRef;
    }

    /**
     * Set the length reference to a new value
     * @param length a reference to the new length
     */
    public void setLength(final AbstractVariableReference length) {
        this.lengthRef = length;
    }

    public abstract JSONObject toJSON() throws JSONException;
}
