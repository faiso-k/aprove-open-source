package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Throw an exception.
 * @author Marc Brockschmidt
 */
public class AThrow extends OpCode {
    /**
     * @return String representation of this opcode
     */
    @Override
    public String toString() {
        return "throw";
    }

    /**
     * Store the exception in the resulting state, so that it is marked as
     * "don't evaluate me, handle the exception!".
     * @param curState The old state
     * @return the single frame that is the result of evaluation (handling the
     * thrown exception is done in the class OpCode)
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State curState) {
        final State newState = curState.clone();

        /*
         * Get the exception from the stack.
         */
        final AbstractVariableReference oR = newState.getCurrentStackFrame().popOperandStack();

        // Mark the state, the exception must be handled (even if it is null)
        newState.getCurrentStackFrame().setException(oR);

        // clear operand stack
        newState.getCurrentStackFrame().getOperandStack().getStack().clear();

        return new Pair<>(newState, new EvaluationEdge());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<OpCode> getAllPossibleSuccessors() {
        return Collections.emptySet();
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
