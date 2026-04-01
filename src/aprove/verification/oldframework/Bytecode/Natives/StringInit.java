package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.runtime.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Predefined method for the constructors of java.lang.String
 */
public class StringInit extends PredefinedMethod {

    private int numArgs;
    private int stackPosUpperSizeBound;

    public StringInit(int numArgs, int stackPosUpperSizeBound) {
        this.numArgs = numArgs;
        this.stackPosUpperSizeBound = stackPosUpperSizeBound;
    }

    @Override
    public Optional<List<String>> getArgs() {
        List<String> res = new ArrayList<>();
        for (int i = 0; i <= numArgs; i++) {
            res.add("arg" + i);
        }
        return Optional.of(res);
    }

    public SimplePolynomial getUpperSizeBound() {
        List<String> args = getArgs().get();
        return SimplePolynomial.create(args.get(args.size() - 1 - stackPosUpperSizeBound));
    }

    public SimplePolynomial getLowerSizeBound() {
        return SimplePolynomial.ZERO;
    }

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        assert isApplicable(s);
        AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(numArgs);
        State newState = s.clone();
        AbstractInstance av = new AbstractInstance();
        AbstractVariableReference newStringRef = newState.createReferenceAndAdd(av, stringRef.getPrimitiveType());
        newState.replaceReference(stringRef, newStringRef);
        newState.getHeapAnnotations().setExistenceIsKnown(newStringRef);
        newState.getHeapAnnotations().setAbstractType(newStringRef, new AbstractType(s.getClassPath(), FuzzyClassType.FT_JAVA_LANG_STRING.toConcrete()));
        newState.getHeapAnnotations().setReachableTypes(newStringRef, new AbstractType(s.getClassPath(), FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract()));
        for (int i = 0; i <= numArgs; i++) {
            newState.getCurrentStackFrame().popOperandStack();
        }
        newState.getCurrentStackFrame().setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        EdgeInformation info = new EvaluationEdge();
        addSizeBound(s, info, newStringRef, Optional.of(getLowerSizeBound()), Optional.of(getUpperSizeBound()));
        return new Pair<>(newState, info);
    }

    @Override
    public boolean isApplicable(State s) {
        if (s.getTerminationGraph().getGoal() == HandlingMode.Termination) {
            return false;
        }
        AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(numArgs);
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
        //get args
        final LinkedList<AbstractVariableReference> poppedRefs = new LinkedList<>();
        for (int i = 0; i < this.numArgs; i++) {
            poppedRefs.add(preEval.getCurrentStackFrame().getOperandStack().peek(i));
        }
        //push args
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
