/**
 *
 */
package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Pseudo-method returning a constant integer value. Used for hashCode() and
 * similar things.
 * @author Christian von Essen
 */
public class ConstantIntReturn extends PredefinedMethod {
    /**
     * (Constant) integer value to return.
     */
    private final AbstractInt returnValue;

    /**
     * Type of the returned integer.
     */
    private final OperandType resultType;

    /**
     * How many operand stack elements should be removed.
     */
    private final int popNumber;

    /**
     * Creates a new pseudo-method returning a constant integer value (range).
     * Used for
     * @param i integer value to return.
     * @param resType Type of the returned integer.
     * @param popMe how many operand stack elements should be removed
     */
    public ConstantIntReturn(final AbstractInt i, final OperandType resType, final int popMe) {
        this.returnValue = i;
        this.resultType = resType;
        this.popNumber = popMe;
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();
        final OperandStack opStack = newState.getCurrentStackFrame().getOperandStack();
        for (int i = 0; i < this.popNumber; i++) {
            opStack.pop();
        }
        final AbstractVariableReference newRef = newState.createReferenceAndAdd(this.returnValue, this.resultType);
        opStack.push(newRef);
        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
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
        preEvalInst.getCurrentStackFrame().popOperandStack();
        final LinkedList<AbstractVariableReference> poppedRefs = new LinkedList<>();
        for (int i = 0; i < this.popNumber; i++) {
            poppedRefs.add(preEval.getCurrentStackFrame().getOperandStack().peek(i));
        }
        final Iterator<AbstractVariableReference> it = poppedRefs.descendingIterator();
        while (it.hasNext()) {
            preEvalInst
                .getCurrentStackFrame()
                .getOperandStack()
                .push(State.mapOrCopyRef(preEval, preEvalInst, it.next(), refMap));
        }
        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }

}
