package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the pop(2) opcode, handling removal of words
 * from the operand stack.
 * @author Christian von Essen
 */
public class StackPop extends OpCode {
    /**
     * pop takes one word from the stack, pop2 two words, which either means two
     * one-word values or one two-word value such as an long or double.
     */
    private final boolean popTwoWords;

    /**
     * Constructor for the stack pop(2) opcodes.
     * @param pop2 true iff two elements should be popped
     */
    public StackPop(final boolean pop2) {
        this.popTwoWords = pop2;
    }

    /** { @inheritDoc } */
    @Override
    public String toString() {
        return (this.popTwoWords) ? "pop (two words)" : "pop";
    }

    /** { @inheritDoc } */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        final State newState = state.clone();
        final StackFrame curFrame = newState.getCurrentStackFrame();

        //Pop one element:
        AbstractVariableReference ref = curFrame.popOperandStack();
        final AbstractVariable av = state.getAbstractVariable(ref);

        //If this was a 2-word value, ensure that we were allowed to pop two words:
        if (av instanceof AbstractNumber && ref.getPrimitiveType().getWords() > 1) {
            assert (this.popTwoWords) : "Could only pop two words, but was supposed to only pop one: Broken Bytecode";
            // We popped one word, we might need to pop another one:
        } else if (this.popTwoWords) {
            //Pop the second value:
            ref = curFrame.popOperandStack();
            //Check that we didn't pop a third word this time:
            assert (ref.getPrimitiveType().getWords() == 1) : "Could only pop three words, but was supposed to only pop two: Broken Bytecode";
        }

        curFrame.setCurrentOpCode(this.getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();

        if (this.popTwoWords) {
            //Un-pop the second value first (so that it's below...):
            final AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(1);
            curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
        }

        // Un-Pop the first value:
        final AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(0);
        curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));

        curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        if (popTwoWords) {
            return 2;
        } else {
            return 1;
        }
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
