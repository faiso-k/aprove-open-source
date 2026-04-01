package aprove.verification.oldframework.Bytecode.OpCodes;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Do nothing.
 * @author Carsten Otto
 */
public final class Nop extends OpCode {
    /**
     * @return String representation of this {@link Nop} opcode.
     */
    @Override
    public String toString() {
        return "NOP";
    }

    /**
     * Just advance the current opcode.
     * @param state The old state
     * @return a list with exact one successor state created by this operation.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        //Do we need to refine? No!
        final State newState = state.clone();

        newState.setCurrentOpCode(this.getNextOp());

        final EvaluationEdge info = new EvaluationEdge();
        return new Pair<>(newState, info);
    }

    @Override
    public int getNumberOfArguments() {
        return 0;
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
