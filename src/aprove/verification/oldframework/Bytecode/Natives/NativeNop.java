/**
 *
 */
package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This implementation does nothing to a state except popping elements from the stack and
 * going to the next opcode
 *
 * @author Christian von Essen.
 */
public class NativeNop extends PredefinedMethod {
    /**
     * Number of arguments to pop from the operand stack.
     */
    private final int argumentNumber;

    /**
     * Iff true, the opcode is set the the following opcode
     */
    private final boolean advanceOpcode;

    /**
     * @param args number of arguments this native (pseudo-)method should pop from the stack.
     */
    public NativeNop(final int args) {
        this(args, true);
    }

    /**
     * @param args number of arguments this native (pseudo-)method should pop from the stack.
     * @param advanceOpcodeParam iff true, the opcode is set the the following opcode
     */
    public NativeNop(final int args, final boolean advanceOpcodeParam) {
        this.argumentNumber = args;
        this.advanceOpcode = advanceOpcodeParam;
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();
        if (this.advanceOpcode) {
            newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        }
        for (int i = 0; i < this.argumentNumber; i++) {
            newState.getCurrentStackFrame().getOperandStack().pop();
        }
        return new Pair<>(newState, new EvaluationEdge());
    }

    /** {@inheritDoc} */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final LinkedList<AbstractVariableReference> poppedRefs = new LinkedList<>();
        for (int i = 0; i < this.argumentNumber; i++) {
            poppedRefs.add(preEval.getCurrentStackFrame().getOperandStack().peek(i));
        }
        final Iterator<AbstractVariableReference> it = poppedRefs.descendingIterator();
        while (it.hasNext()) {
            preEvalInst
                .getCurrentStackFrame()
                .getOperandStack()
                .push(State.mapOrCopyRef(preEval, preEvalInst, it.next(), refMap));
        }

        if (this.advanceOpcode) {
            preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        }
        return preEvalInst;
    }

}
