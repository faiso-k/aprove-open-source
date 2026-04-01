package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the getClass() method in java.lang.Object. Returns a class
 * object for the class an object is implementing. Handles non-concrete types
 * using possible equalities.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class GetClass extends PredefinedMethod {
    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();

        final AbstractVariableReference instRef = newState.getCallStack().getTop().getOperandStack().pop();

        final AbstractType t = s.getAbstractType(instRef);
        final AbstractVariableReference classRef;
        if (t.isConcrete() && t.getMinimalClass() != null) {
            final FuzzyType type = t.getMinimalClass();
            classRef = JLClassHelper.addConstantClassToStateOrThrow(newState, type);
        } else {
            classRef = JLClassHelper.addAbstractClassToStateOrThrow(newState);
        }

        if (classRef == null) {
            return new Pair<>(newState, new EvaluationEdge());
        }

        newState.getCurrentStackFrame().getOperandStack().push(classRef);
        newState.getCurrentStackFrame().setCurrentOpCode(s.getCurrentOpCode().getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        return ObjectRefinement.forInitialization(ClassName.Important.JAVA_LANG_CLASS, s, result);
    }

}
