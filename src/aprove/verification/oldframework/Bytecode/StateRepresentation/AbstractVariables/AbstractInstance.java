package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Abstract representation of instances in our symbolic interpretation.
 *
 * @author Marc Brockschmidt
 */
public class AbstractInstance extends ObjectInstance {
    /**
     * Create a new AbstractInstance.
     */
    public AbstractInstance() {

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getField(
        final State state,
        final AbstractVariableReference myRef,
        final ClassName className,
        final String name)
    {

        //Get type for the field content and create a fitting value
        final IClass instClass = state.getClassPath().getClass(className);
        final Field readField = instClass.getField(name);

        final AbstractVariableReference newValRef =
            VariableInitialization.getFreshVarFor(
                FuzzyType.parseTypeDescriptor(readField.getDescriptor()),
                myRef,
                state,
                FieldValueSettings.GENERAL_VALUE);

        if (newValRef.pointsToReferenceType()) {
            VariableInitialization.annotateAsFreshChildRefs(state, myRef, Collections
                .singleton(new Pair<HeapEdge, AbstractVariableReference>(
                    new InstanceFieldEdge(className, name),
                    newValRef)), null, null);

            // make clear that newValRef is somewhere behind myRef
            state.getHeapAnnotations().getJoiningStructures().add(newValRef, myRef);
        }

        return newValRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<DefiniteReachabilityAnnotationCreation> putField(
        final State state,
        final AbstractVariableReference myRef,
        final ClassName className,
        final String name,
        final AbstractVariableReference varRef)
    {
        //Mark the change, as this will not be noted in the actual representation
        final HeapPositions heapPos = new HeapPositions(state);
        for (final StackFrame sf : state.getCallStack().getStackFrameList()) {
            sf.getInputReferences().markInstanceFieldAsChanged(heapPos, myRef, new FieldIdentifier(className, name), varRef, null);
        }

        //No annotation fixes for primitives, so we are done:
        if (!varRef.pointsToReferenceType()) {
            return Collections.emptySet();
        }

        return AnnotationFixups
            .annotateAsNewAbstractChild(state, myRef, new InstanceFieldEdge(className, name), varRef);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "(?)";
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        throw new JSONException("JSON representation of abstract instances not implemented yet.");
    }
}
