package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The opcodes monitorenter and monitorexit.
 * @author cotto
 */
public class MonitorEnterExit extends OpCode {

    /**
     * We need to know if the object exists.
     * @param s the state to refine
     * @param result the refined states
     * @return true iff we had to refine the information
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        final AbstractVariableReference topRef = s.getCurrentStackFrame().peekOperandStack(0);
        if (ObjectRefinement.forExistence(topRef, s, result)) {
            return true;
        }
        if (topRef.isNULLRef()) {
            return ObjectRefinement.forInitialization(Important.NPE_EXC, s, result);
        }
        return false;
    }

    /**
     * Do whatever monitorenter or monitorexit does.
     * @param s the state
     * @return the states after evaluation
     */
    @Override
    public Pair<State, EdgeInformation> evaluate(final State s) {
        final State newState = s.clone();
        final StackFrame frame = newState.getCurrentStackFrame();
        final AbstractVariableReference topRef = frame.peekOperandStack(0);
        EdgeInformation edge;
        if (topRef.isNULLRef()) {
            OpCode.throwException(newState, NPE_EXC);
            edge = new MethodStartEdge();
        } else {
            frame.popOperandStack();
            frame.setCurrentOpCode(this.getNextOp());
            edge = new EvaluationEdge();
        }
        return new Pair<>(newState, edge);
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
