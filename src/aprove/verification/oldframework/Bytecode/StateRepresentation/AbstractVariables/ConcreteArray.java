package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * A concrete representation of arrays in our symbolic interpretation, depending
 * on a known literal length. Objects are actual references. All accesses need
 * to be done using literal integers, or this array is automatically converted
 * to an abstract one.
 *
 * @author Marc Brockschmidt
 */
public final class ConcreteArray extends Array {
    /**
     * Length of this array.
     */
    private final int length;

    /**
     * The actual data: Array of references.
     */
    private AbstractVariableReference[] data;

    /**
     * Create a new array.
     * @param lengthR Length (as variable reference)
     * @param s the state in which this array is created. Needs to define a
     * literal for <code>lengthR</code>.
     * @param type the type of the elements in this array. If not null, the
     * corresponding default values will be stored in the array (and the state
     * will be updated with the corresponding reference and value).
     */
    public ConcreteArray(final AbstractVariableReference lengthR, final State s, final FuzzyType type) {
        super(lengthR);
        final AbstractVariable lengthVar = s.getAbstractVariable(lengthR);
        assert (lengthVar instanceof AbstractInt);
        final AbstractInt lengthVarInt = (AbstractInt) lengthVar;
        assert (lengthVarInt.isLiteral()) : "Trying to create concrete" + " array with non-literal length";
        assert (lengthVarInt.getLiteral().signum() >= 0);
        assert (lengthVarInt.getLiteral().compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0);
        this.length = lengthVarInt.getLiteral().intValue();
        this.data = new AbstractVariableReference[this.length];
        if (type != null) {
            for (int i = 0; i < this.length; i++) {
                this.data[i] = VariableInitialization.getFreshVarFor(type, null, s, FieldValueSettings.DEFAULT_VALUE);
            }
        }
    }

    /**
     * @return the actual length of the enclosed array.
     */
    public int getLiteralLength() {
        return this.length;
    }

    /**
     * Returns a deep (!) copy of this {@link ConcreteArray} object
     * @return Deep copy of this object
     */
    @Override
    public ConcreteArray clone() {
        final ConcreteArray clone = (ConcreteArray) super.clone();
        // AVRs are immutable
        clone.data = this.data.clone();
        return clone;
    }

    /** {@inheritDoc} */
    @Override
    public Map<AbstractVariableReference, Integer> getReferences() {
        final Map<AbstractVariableReference, Integer> res = new LinkedHashMap<AbstractVariableReference, Integer>();
        res.put(super.getLength(), 1);

        for (int index = 0; index < this.length; index++) {
            final AbstractVariableReference ref = this.data[index];
            if (ref != null) {
                if (res.containsKey(ref)) {
                    res.put(ref, res.get(ref) + 1);
                } else {
                    res.put(ref, 1);
                }
            }
        }
        return res;
    }

    /**
     * @param index Some index into the enclosed array.
     * @param valueRef Value to put into array[index]
     */
    public void put(final int index, final AbstractVariableReference valueRef) {
        this.data[index] = valueRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<DefiniteReachabilityAnnotationCreation> store(
        final State state,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef,
        final AbstractVariableReference valueRef,
        final boolean isPrimitive)
    {
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();

        //Get the index, find out if we can do this properly:
        final AbstractInt indexVar = (AbstractInt) state.getAbstractVariable(indexRef);

        boolean writingConcreteArray = false;
        if (valueRef.pointsToArray()) {
            final AbstractVariable var = state.getAbstractVariable(valueRef);
            if (var instanceof ConcreteArray) {
                writingConcreteArray = true;
            }
        }

        //Easy case:
        if (indexVar.isLiteral() && !writingConcreteArray) {
            final int index = indexVar.getLiteral().intValue();
            final AbstractVariableReference oldRef = this.get(state, arrayRef, index);
            if (!oldRef.equals(valueRef)) {
                final HeapPositions heapPos = new HeapPositions(state);
                for (final StackFrame sf : state.getCallStack().getStackFrameList()) {
                    sf.getInputReferences().markArrayAsChanged(heapPos, arrayRef, indexRef, valueRef, oldRef);
                }

                final State cloneAfterWrite = state.clone();
                final ConcreteArray arrayAfter = (ConcreteArray) cloneAfterWrite.getAbstractVariable(arrayRef);
                arrayAfter.put(index, valueRef);

                newDefReach.addAll(AnnotationFixups.annotateAsNewConcreteChild(state, arrayRef, new ArrayMemberEdge(
                    index), valueRef, cloneAfterWrite, true));
                this.put(index, valueRef);
            }
        } else {
            /*
             * Complicated case: Auto-convert to an abstract array:
             * (1) Create a new AbstractArray in abstrArrayRef
             * (2) Replace all occurrences of arrayRef with abstrArrayRef
             * (3) Reinsert all values currently stored in this array into
             *     the new array
             * (4) Finally add the new value.
             */
            final AbstractArray aA = new AbstractArray(super.getLength());

            /*
             * We need to still have the concrete information about the old
             * array and its content to handle annotations due to the
             * converting writes.
             */
            final AbstractVariableReference dummyRef =
                state.createReferenceAndAdd(state.getAbstractVariable(arrayRef), arrayRef.getPrimitiveType());
            state.setAbstractType(dummyRef, state.getAbstractType(arrayRef));
            state.getHeapAnnotations().setReachableTypes(
                dummyRef,
                state.getHeapAnnotations().getReachableTypes(arrayRef));
            state.getCurrentStackFrame().pushOperandStack(dummyRef);

            state.removeAbstractVariable(arrayRef);
            state.addAbstractVariable(arrayRef, aA);

            state.gc();

            for (int curIndex = 0; curIndex < this.length; curIndex++) {
                if (this.data[curIndex] != null) {
                    final AbstractVariableReference curIndexRef =
                        state.createReferenceAndAdd(AbstractInt.create(curIndex), OperandType.INTEGER);
                    newDefReach.addAll(aA.store(state, arrayRef, curIndexRef, this.data[curIndex], isPrimitive));
                }
            }
            newDefReach.addAll(aA.store(state, arrayRef, indexRef, valueRef, isPrimitive));
            state.getCurrentStackFrame().popOperandStack();
        }
        if (!valueRef.isNULLRef() && valueRef.pointsToReferenceType()) {
            state.getHeapAnnotations().addReachableTypes(arrayRef, state.getAbstractType(valueRef), state.getClassPath(), state.getJBCOptions());
        }
        return newDefReach;
    }

    /**
     * @param state state in which this array is used (needed for variable
     *  lookups)
     * @param arrayRef {@link AbstractVariableReference} to this array (needed
     *  for type lookups)
     * @param index index of the stored element
     * @return an {@link AbstractVariableReference} to a fitting abstract
     *  variable, either freshly created or re-used from former accesses of this
     *  array.
     */
    public AbstractVariableReference get(final State state, final AbstractVariableReference arrayRef, final int index) {
        final AbstractVariableReference resVarRef;

        final AbstractType arrayT = state.getAbstractType(arrayRef);
        final AbstractType enclosedType = arrayT.getEnclosedTypes(state.getClassPath(), state.getJBCOptions());
        assert (this.data.length > index);
        if (this.data[index] != null) {
            resVarRef = this.data[index];
        } else {
            //Get a new copy of the default value:
            final boolean hasPrimitive = enclosedType.containsPrimitiveType();

            if (hasPrimitive) {
                assert (enclosedType.isConcrete()) : "ERROR: Variable must be a known primitive type.";
                final FuzzyType t = enclosedType.getPrimitiveType();
                resVarRef = VariableInitialization.getFreshVarFor(t, arrayRef, state, FieldValueSettings.DEFAULT_VALUE);
            } else {
                resVarRef = AbstractVariableReference.NULLREF;
            }
        }

        return resVarRef;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractVariableReference load(
        final State state,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef)
    {
        //Get the index, find out if we can do this properly:
        final AbstractInt indexVar = (AbstractInt) state.getAbstractVariable(indexRef);

        final AbstractVariableReference resVarRef;

        //Easy case:
        if (indexVar.isLiteral()) {
            resVarRef = this.get(state, arrayRef, indexVar.getLiteral().intValue());
        } else {
            /*
             * Complicated case: Get new ref, mark it as possibly equal to the
             * rest.
             */
            resVarRef = Array.loadFreshVar(state, arrayRef);

            //Now add possible equalities to all values which might be
            //indexed:
            for (int index = 0; index < this.length; index++) {
                if (this.data[index] != null && indexVar.containsLiteral(index)) {
                    state
                        .getHeapAnnotations()
                        .getEqualityGraph()
                        .addPossibleEquality(state, this.data[index], resVarRef);
                }
            }
        }

        return resVarRef;
    }

    /** {@inheritDoc} */
    @Override
    public String toString(
        final AbstractVariableReference myRef,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        StringBuilder t = new StringBuilder();
        StringBuilder concreteString = new StringBuilder();
        concreteString.append("\"");

        if (this.length == 0 || state == null) {
            t.append("length "
                + PrettyVariablePrinter.prettyPrint(super.getLength(), varUsers, state, shortRepresentation));
            //t.append("length: " + this.lengthRef);
        } else {
            final AbstractType at = state.getAbstractType(myRef);
            final AbstractType enclosed = at.getEnclosedTypes(state.getClassPath(), state.getJBCOptions());
            final boolean isCharArray =
                enclosed.isConcrete()
                    && enclosed.containsPrimitiveType()
                    && enclosed.getPrimitiveType().getPrimitiveType().equals(OperandType.CHAR);
            boolean isFirst = true;
            t.append("{");
            for (int index = 0; index < this.length; index++) {
                if (!isFirst) {
                    t.append(", ");
                }
                if (isCharArray && concreteString != null) {
                    if (this.data[index] != null) {
                        final AbstractInt intV = (AbstractInt) state.getAbstractVariable(this.data[index]);
                        if (intV.isLiteral()) {
                            final char literalChar = (char) intV.getLiteral().intValue();
                            String charString = String.valueOf(literalChar);
                            if (literalChar < 33 || literalChar > 126) {
                                charString = ".";
                            }
                            concreteString.append(charString);
                        } else {
                            concreteString = null;
                        }
                    } else {
                        concreteString = null;
                    }
                }

                if (this.data[index] != null) {
                    t.append(PrettyVariablePrinter.prettyPrint(
                        this.get(state, myRef, index),
                        varUsers,
                        state,
                        shortRepresentation));
                } else {
                    t.append("NULL");
                }
                isFirst = false;
            }
            t.append("}");
            if (concreteString != null && concreteString.length() > 1) {
                t = concreteString;
                t.append("\"");
            }
        }

        return t.toString();
    }

    /** {@inheritDoc} */
    @Override
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        super.replaceReference(oldRef, newRef);
        for (int index = 0; index < this.length; index++) {
            if (this.data[index] != null) {
                if (this.data[index].equals(oldRef)) {
                    this.data[index] = newRef;
                }
            }
        }
    }

    /**
     * @return the stored references
     */
    public AbstractVariableReference[] getData() {
        return this.data;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        final JSONArray dataArr = new JSONArray();
        for (final AbstractVariableReference ref : this.data) {
            dataArr.put(ref.toString());
        }
        res.put("length", this.getLength().toString());
        res.put("data", dataArr);
        return res;
    }
}
