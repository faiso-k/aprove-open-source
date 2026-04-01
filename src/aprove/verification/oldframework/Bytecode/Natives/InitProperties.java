package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author cotto
 */
public class InitProperties extends PredefinedMethod {

    /**
     * {@inheritDoc}
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        /*
         * The native implementation adds a bunch of complicated entries to the
         * map. Instead of doing the same, we just remove all field information
         * (e.g. the map's content) and continue with an unknown object.
         */
        final State newState = s.clone();
        final AbstractVariableReference propRef = newState.getCurrentStackFrame().peekOperandStack(0);
        newState.removeAbstractVariable(propRef);
        final ConcreteInstance aI = ConcreteInstance.newJLO(newState);
        newState.addAbstractVariable(propRef, aI);
        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }


}
