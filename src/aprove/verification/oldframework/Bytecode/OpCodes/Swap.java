package aprove.verification.oldframework.Bytecode.OpCodes;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of the operand stack swap opcode (swapping the two topmost
 * values).
 * @author Christian von Essen
 */
public class Swap extends OpCode {
    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "Swap";
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        //Get current stack frame:
        final State newState = state.clone();
        final StackFrame curFrame = newState.getCurrentStackFrame();

        final AbstractVariableReference first = curFrame.popOperandStack();
        final AbstractVariableReference second = curFrame.popOperandStack();
        curFrame.pushOperandStack(first);
        curFrame.pushOperandStack(second);

        if (Globals.useAssertions) {
            final AbstractVariable firstVal = state.getAbstractVariable(first);
            final AbstractVariable secondVal = state.getAbstractVariable(second);
            assert (!(firstVal instanceof AbstractNumber && first.getPrimitiveType().getWords() > 1)) : "Swap doesn't handle two-word values, but "
                + first
                + " references one.";

            assert (!(secondVal instanceof AbstractNumber && second.getPrimitiveType().getWords() > 1)) : "Swap doesn't handle two-word values, but "
                + second
                + " references one.";
        }

        //Now finish, move through the code:
        curFrame.setCurrentOpCode(this.getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    @Override
    public int getNumberOfArguments() {
        return 2;
    }

    @Override
    public int getNumberOfOutputs() {
        return 2;
    }

}
