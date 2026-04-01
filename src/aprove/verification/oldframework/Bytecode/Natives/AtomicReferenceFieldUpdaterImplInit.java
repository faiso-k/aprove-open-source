package aprove.verification.oldframework.Bytecode.Natives;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Native implementation of the AtomicReferenceFieldUpdaterImpl constructor
 * (saving the relevant values).
 *
 * @author Marc Brockschmidt
 */
public class AtomicReferenceFieldUpdaterImplInit extends PredefinedMethod {
    /**
     * Creates a new pseudo-method setting the atomic integer value.
     */
    public AtomicReferenceFieldUpdaterImplInit() {
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();

        final AbstractVariableReference fieldNameRef = newState.getCallStack().getTop().getOperandStack().pop();
        final AbstractVariableReference fieldTypeRef = newState.getCallStack().getTop().getOperandStack().pop();
        final AbstractVariableReference instTypeRef = newState.getCallStack().getTop().getOperandStack().pop();
        final AbstractVariableReference updaterRef = newState.getCallStack().getTop().getOperandStack().pop();

        final String fieldName = newState.getConcreteString(fieldNameRef);
        final FuzzyType fieldTypeName = newState.getClassInstance(fieldTypeRef);
        final FuzzyType instTypeName = newState.getClassInstance(instTypeRef);

        assert (fieldName != null && fieldTypeName != null && instTypeName != null) : "Trying to construct atomic reference field updater for abstract types and fields.";

        assert instTypeName instanceof FuzzyClassType;

        newState.getAtomicFieldUpdaterInfo().addUpdater(updaterRef, (FuzzyClassType) instTypeName, fieldName, fieldTypeName);

        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

}
