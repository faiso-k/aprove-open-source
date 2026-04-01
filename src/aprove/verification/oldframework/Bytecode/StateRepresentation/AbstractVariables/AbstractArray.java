package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.util.*;

import org.json.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Representation of arrays in our symbolic interpretation, realized by an
 * AbstractInt holding the length and a type signature of the enclosed objects.
 * @author Marc Brockschmidt
 */
public final class AbstractArray extends Array {
    /**
     * Create a new array.
     * @param length Length (as AbstractInt) of the array.
     */
    public AbstractArray(final AbstractVariableReference length) {
        super(length);
    }

    /**
     * Returns a deep (!) copy of this {@link AbstractArray} object
     * @return Deep copy of this object
     */
    @Override
    public AbstractArray clone() {
        final AbstractArray clone = (AbstractArray) super.clone();
        return clone;
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

        final HeapPositions heapPos = new HeapPositions(state);
        for (final StackFrame sf : state.getCallStack().getStackFrameList()) {
            sf.getInputReferences().markArrayAsChanged(heapPos, arrayRef, indexRef, valueRef, null);
        }

        // no need to deal with annotations for primitive values
        if (isPrimitive) {
            return Collections.emptySet();
        }

        if (Globals.useAssertions) {
            assert (state.getAbstractVariable(indexRef) instanceof AbstractInt);
        }

        // if we know that we definitely overwrite some reference, remove it before we calculate the annotations
        if (!state.getHeapAnnotations().isPossiblyNonTree(arrayRef)) {
            /*
             * With non-tree shapes we could have a[x] = a[y], so even after the write a[x] = null the object is
             * contained in the array.
             */

            final AbstractVariableReference content = state.getHeapAnnotations().getArrayInfo().get(arrayRef, indexRef);
            if (content != null) {
                /*
                 * Remove array[index] joins x, because we overwrite x now (dropping the connection described by the
                 * joins annotation)
                 */
                state.getHeapAnnotations().getJoiningStructures().remove(arrayRef, content);
            }
        }

        // remove information about whatever we had in the array before the write
        state.getHeapAnnotations().getArrayInfo().remove(arrayRef, indexRef);

        final Collection<DefiniteReachabilityAnnotationCreation> changedAnnotations =
            AnnotationFixups.annotateAsNewAbstractChild(state, arrayRef, UnknownArrayMemberEdge.INSTANCE, valueRef);

        // for abstract writes into an array, we may add a definite reachability annotation
        if (!valueRef.isNULLRef() && valueRef.pointsToReferenceType()) {
            state.getHeapAnnotations().getArrayInfo().add(arrayRef, indexRef, valueRef);
        }

        return changedAnnotations;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractVariableReference load(
        final State state,
        final AbstractVariableReference arrayRef,
        final AbstractVariableReference indexRef)
    {
        if (Globals.useAssertions) {
            assert (state.getAbstractVariable(indexRef) instanceof AbstractInt) : "Please use ints to index arrays. Thanks.";
        }

        final AbstractVariableReference result = Array.loadFreshVar(state, arrayRef);

        // for abstract reads from an array, we may add more information
        if (!result.isNULLRef() && result.pointsToReferenceType()) {
            state.getHeapAnnotations().getArrayInfo().add(arrayRef, indexRef, result);
        }

        // make clear that result is somewhere behind arrayRef
        if (result.pointsToReferenceType()) {
            state.getHeapAnnotations().getJoiningStructures().add(result, arrayRef);
        }
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public String toString(
        final AbstractVariableReference myRef,
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        final StringBuilder t = new StringBuilder();
        t
            .append("length "
                + PrettyVariablePrinter.prettyPrint(super.getLength(), varUsers, state, shortRepresentation));
        return t.toString();
    }

    /** {@inheritDoc} */
    @Override
    public Map<AbstractVariableReference, Integer> getReferences() {
        return Collections.singletonMap(super.getLength(), 1);
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("length", this.getLength().toString());
        return res;
    }
}
