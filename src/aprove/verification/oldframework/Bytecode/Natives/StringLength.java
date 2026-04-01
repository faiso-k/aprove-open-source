package aprove.verification.oldframework.Bytecode.Natives;

import java.util.Map;

import aprove.runtime.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Predefined method for java.lang.String.length()I
 */
public class StringLength extends PredefinedMethod {

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        assert isApplicable(s);
        State newState = s.clone();
        AbstractVariableReference stringRef = newState.getCurrentStackFrame().popOperandStack();
        String concString = newState.getConcreteString(stringRef);
        AbstractInt res;
        if (concString != null) {
            res = AbstractInt.create(concString.length());
        } else {
            res = AbstractInt.create(IntervalBound.ZERO, IntegerType.UNBOUND.getUpper(), IntervalBound.ZERO, IntegerType.JAVA_INT.getUpper(), 0, 0);
        }
        AbstractVariableReference resRef = newState.createReferenceAndAdd(res, OperandType.INTEGER);
        newState.getCurrentStackFrame().pushOperandStack(resRef);
        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        EdgeInformation info = new EvaluationEdge();
        info.add(new JBCIntegerRelation(resRef, IntegerRelationType.GE, AbstractInt.getZero()));
        info.add(new SizeRelationInformation(stringRef, IntegerRelationType.GE, SimplePolynomial.create(resRef.toString())));
        return new Pair<>(newState, info);
    }

    @Override
    public boolean isApplicable(State s) {
        if (s.getTerminationGraph().getGoal() == HandlingMode.Termination) {
            return false;
        }
        AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(0);
        if (stringRef.isNULLRef() || s.getHeapAnnotations().isMaybeExisting(stringRef)) {
            return false;
        }
        return true;
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();

        //pop result
        preEvalInst.getCurrentStackFrame().popOperandStack();
        //push String
        AbstractVariableReference stringRef = preEval.getCurrentStackFrame().peekOperandStack(0);
        preEvalInst.getCurrentStackFrame().pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, stringRef, refMap));
        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }
}
