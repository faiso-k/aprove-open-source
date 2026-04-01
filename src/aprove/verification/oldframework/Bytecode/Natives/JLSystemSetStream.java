package aprove.verification.oldframework.Bytecode.Natives;

import java.util.Map;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Native implementation of java.lang.System.set(In|Out|Err).
 *
 * @author Marc Brockschmidt
 */
public class JLSystemSetStream extends PredefinedMethod {
    /**
     * The name of the field to set (either "in", "out" or "err").
     */
    private final String fieldName;

    /**
     * Creates a new pseudo-method setting the output/input fields.
     * @param fName the field to set.
     */
    public JLSystemSetStream(final String fName) {
        assert (fName.equals("in") || fName.equals("out") || fName.equals("err")) : "Trying to set weird field in java.lang.System";
        this.fieldName = fName;
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();
        final OperandStack opStack = newState.getCurrentStackFrame().getOperandStack();

        final AbstractVariableReference newValRef = opStack.pop();

        newState.getStaticFields().set(Important.JAVA_LANG_SYSTEM.getClassName(), this.fieldName, newValRef);

        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    @Override
    public State reverseEvaluation(State preEval, State postEval, State postEvalInst,
            Map<AbstractVariableReference, AbstractVariableReference> refMap) {
        final State preEvalInst = postEvalInst.clone();
        final ClassName jlSystem = Important.JAVA_LANG_SYSTEM.getClassName();
        
        //push field value on stack
        preEvalInst.getCurrentStackFrame().pushOperandStack(preEvalInst.getStaticFields().get(jlSystem, this.fieldName));
        //restore field Value
        preEvalInst.getStaticFields().set(
            jlSystem,
            this.fieldName,
            State.mapOrCopyRef(
                preEval,
                preEvalInst,
                preEval.getStaticFields().get(jlSystem, this.fieldName),
                refMap));

        preEvalInst.setCurrentOpCode(preEval.getCurrentOpCode());
        return preEvalInst;
    }

}
