package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AtomicFieldUpdaterInfo.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of get function in AtomicReferenceFieldUpdaterImpl. As we
 * are not able to handle multithreading anyway, we can avoid jumping through
 * the shiny reflection hoops that are used in the original Sun/Oracle
 * implementation.
 *
 * @author Marc Brockschmidt
 */
public class AtomicReferenceFieldGet extends PredefinedMethod {
    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();
        final OperandStack opStack = newState.getCurrentStackFrame().getOperandStack();

        //Get the instance to work on:
        final AbstractVariableReference instToReadRef = opStack.pop();
        final ObjectInstance instToRead = (ObjectInstance) newState.getAbstractVariable(instToReadRef);

        //Get the updater ref holding the information:
        final AbstractVariableReference updaterRef = opStack.pop();
        final AtomicFieldUpdaterData updaterData = newState.getAtomicFieldUpdaterInfo().get(updaterRef);

        assert (instToReadRef != null && updaterRef != null) : "Trying to use atomic reference field updater, but miss information";

        //Get the field, put it on the stack:
        final AbstractVariableReference fieldValRef =
            instToRead.getField(
                newState,
                instToReadRef,
                updaterData.getInstanceType().getMinimalClass(),
                updaterData.getFieldName());

        opStack.push(fieldValRef);

        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        return new Pair<State, EvaluationEdge>(newState, new EvaluationEdge());
    }
}
