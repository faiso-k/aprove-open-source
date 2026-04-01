package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class GetClassLoader extends PredefinedMethod {
    /** { @inheritDoc } */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State clone = s.clone();
        clone.getCallStack().getTop().pushOperandStack(AbstractVariableReference.NULLREF);
        clone.getCurrentStackFrame().setCurrentOpCode(s.getCurrentOpCode().getNextOp());
        return new Pair<>(clone, new EvaluationEdge());
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();
        preEvalInst.getCurrentStackFrame().popOperandStack();
        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }
}
