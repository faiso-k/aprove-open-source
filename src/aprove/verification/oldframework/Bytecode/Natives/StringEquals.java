package aprove.verification.oldframework.Bytecode.Natives;

import java.util.Map;

import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Predefined method for java.lang.String.equals(Ljava/lang/Object;)Z
 */
public class StringEquals extends PredefinedMethod {

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        assert isApplicable(s);
        State newState = s.clone();
        AbstractInt res;
        AbstractVariableReference otherStringRef = newState.getCurrentStackFrame().popOperandStack();
        AbstractVariableReference stringRef = newState.getCurrentStackFrame().popOperandStack();
        if (newState.getConcreteString(stringRef).equals(newState.getConcreteString(otherStringRef))) {
            res = AbstractInt.create(1);
        } else {
            res = AbstractInt.create(0);
        }
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
        AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(1);
        if (stringRef.isNULLRef() || s.getHeapAnnotations().isMaybeExisting(stringRef)) {
            return false;
        }
        AbstractVariableReference otherStringRef = s.getCurrentStackFrame().peekOperandStack(0);
        return s.getConcreteString(otherStringRef) != null && s.getConcreteString(stringRef) != null;
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();

        //pop result
        preEvalInst.getCurrentStackFrame().popOperandStack();
        //push "this" String
        AbstractVariableReference stringRef = preEval.getCurrentStackFrame().peekOperandStack(1);
        preEvalInst.getCurrentStackFrame().pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, stringRef, refMap));
        //push other String
        AbstractVariableReference otherStringRef = preEval.getCurrentStackFrame().peekOperandStack(0);
        preEvalInst.getCurrentStackFrame().pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, otherStringRef, refMap));

        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }
}
