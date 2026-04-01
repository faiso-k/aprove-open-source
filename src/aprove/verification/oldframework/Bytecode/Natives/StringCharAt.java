package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Predefined method for java.lang.String.charAt(I)C.
 */
public class StringCharAt extends PredefinedMethod {

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        assert isApplicable(s);
        State newState = s.clone();
        AbstractVariableReference posRef = newState.getCurrentStackFrame().popOperandStack();
        AbstractVariableReference stringRef = newState.getCurrentStackFrame().popOperandStack();
        AbstractVariable pos = newState.getAbstractVariable(posRef);
        int literalPos = ((LiteralInt) pos).getIntLiteralValue().intValue();
        AbstractInt res = AbstractInt.create(newState.getConcreteString(stringRef).charAt(literalPos));
        AbstractVariableReference resRef = newState.createReferenceAndAdd(res, OperandType.INTEGER);
        newState.getCurrentStackFrame().pushOperandStack(resRef);
        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    @Override
    public boolean isApplicable(State s) {
        if (s.getTerminationGraph().getGoal() == HandlingMode.Termination) {
            return false;
        }
        AbstractVariableReference posRef = s.getCurrentStackFrame().peekOperandStack(0);
        AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(1);
        if (stringRef.isNULLRef() || s.getHeapAnnotations().isMaybeExisting(stringRef)) {
            return false;
        }
        AbstractVariable pos = s.getAbstractVariable(posRef);
        if (!(pos instanceof LiteralInt)) {
            return false;
        }
        int literalPos = ((LiteralInt) pos).getIntLiteralValue().intValue();
        if (literalPos < 0) {
            return false;
        }
        String val = s.getConcreteString(stringRef);
        if (val == null) {
            return false;
        }
        return val.length() > literalPos;
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();

        //pop result
        AbstractVariableReference res = preEvalInst.getCurrentStackFrame().popOperandStack();
        //push String
        AbstractVariableReference stringRef = preEval.getCurrentStackFrame().peekOperandStack(1);
        preEvalInst.getCurrentStackFrame().pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, stringRef, refMap));
        //push index
        AbstractVariableReference indexRef = preEval.getCurrentStackFrame().peekOperandStack(0);
        preEvalInst.getCurrentStackFrame().pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, indexRef, refMap));
        //set the char from string to res
        String oldString = preEvalInst.getConcreteString(stringRef);
        if (oldString != null) {
            AbstractVariable pos = preEvalInst.getAbstractVariable(indexRef);
            int literalPos = ((LiteralInt) pos).getIntLiteralValue().intValue();
            AbstractVariable charr = preEvalInst.getAbstractVariable(res);
            int literalCharI =((LiteralInt) charr).getIntLiteralValue().intValue();
            char literalChar = (char) literalCharI;
            preEvalInst.setConcreteString(stringRef, oldString.substring(0,literalPos)+literalChar+oldString.substring(literalPos+1));
        }

        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }

}
