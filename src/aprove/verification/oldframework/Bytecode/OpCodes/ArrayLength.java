package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the arraylength opcode.
 *
 * @author Marc Brockschmidt
 */
public class ArrayLength extends OpCode {
    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "arraylength";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final AbstractVariableReference aAR = s.getCurrentStackFrame().peekOperandStack(0);

        if (ObjectRefinement.forExistence(aAR, s, out)) {
            return true;
        }

        if (aAR.isNULLRef() && ObjectRefinement.forInitialization(Important.NPE_EXC, s, out)) {
            return true;
        }

        return ArrayRefinement.forArrayRealization(aAR, s, out);
    }

    /**
     * Generates exactly one new state from the current state by returning
     * the length of the array currently on the top of the operand stack
     *
     * @param curState The old state
     * @return a list with exact one successor states created by this operation.
     */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State curState) {
        final State newState = curState.clone();

        final StackFrame frame = newState.getCurrentStackFrame();
        final AbstractVariableReference aAR = frame.peekOperandStack(0);
        final AbstractVariable aA = newState.getAbstractVariable(aAR);
        if (aA.isNULL()) {
            OpCode.throwException(newState, NPE_EXC);
            return new Pair<>(newState, new MethodStartEdge());
        }
        frame.popOperandStack();
        if (aA instanceof Array) {
            frame.pushOperandStack(((Array) aA).getLength());
            frame.setCurrentOpCode(this.getNextOp());
            final EvaluationEdge infoEdge = new EvaluationEdge();
            infoEdge.add(new ArrayLengthInfo(aAR, ((Array) aA).getLength()));
            infoEdge.add(new JBCIntegerRelation(((Array) aA).getLength(), IntegerRelationType.GE, 0));
            return new Pair<>(newState, infoEdge);
        }
        assert (false) : "Trying to compute array length of non-array " + aA;
        return null;
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
        final StackFrame preEvalFrame = preEval.getCurrentStackFrame();
        final StackFrame preEvalInstFrame = preEvalInst.getCurrentStackFrame();

        preEvalInstFrame.getOperandStack().pop();

        final AbstractVariableReference abstrArrayRef = preEvalFrame.getOperandStack().peek(0);
        final AbstractVariableReference concrArrayRef = refMap.get(abstrArrayRef);

        assert (concrArrayRef != null) : "Could not identify accessed array";

        preEvalInstFrame.getOperandStack().push(concrArrayRef);
        preEvalInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
