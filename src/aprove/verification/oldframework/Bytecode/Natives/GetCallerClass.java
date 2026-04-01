package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the getCallerClass() method in sun.reflect.Reflection.
 * Is called with parameter n and returns a class object corresponding to the
 * class of the position of the n-th (0-based counting) class from the top
 * of the stackframe. If n is unknown is bigger than the number of stackframes,
 * returns an unknow class object.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class GetCallerClass extends PredefinedMethod {
    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final AbstractVariableReference intRef = s.getCallStack().getTop().getOperandStack().pop();

        final State newState = s.clone();

        final AbstractInt intVar = (AbstractInt) s.getAbstractVariable(intRef);

        ClassName classToReturn = null;
        if (intVar.isLiteral()) {
            long intVal = intVar.getLiteral().longValue();
            //0 is the stackframe of this method, i.e. the result is known
            if (intVal == 0) {
                classToReturn = ClassName.fromDotted("sun.reflect.Reflection");
            } else {
                intVal--;
                if (newState.getCallStack().size() > intVal) {
                    classToReturn =
                        newState.getCallStack().get((int) intVal).getCurrentOpCode().getMethod().getClassName();
                }
            }
        }

        final AbstractVariableReference classRef;
        if (classToReturn != null) {
            final FuzzyType type = new FuzzyClassType(classToReturn, true);
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

}
