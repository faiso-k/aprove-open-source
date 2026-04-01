package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of ret opcodes, used for returning from subroutines (NOT for
 * returning a value from a method, that's done by Return.java).
 * @author Christian von Essen, Carsten Otto
 */
public class Ret extends OpCode implements LocalVariableUser {
    /**
     * Index in the local variable array of the return address.
     */
    private final int localVarArrIndex;

    /**
     * @param indexOfReturnAdress index to a value in the local variable which
     *  must be a returnAddress, which will then be used to return from the
     *  subroutine.
     */
    public Ret(final int indexOfReturnAdress) {
        this.localVarArrIndex = indexOfReturnAdress;
    }

    /**
     * @return String representation of this {@link Ret} opcode.
     */
    @Override
    public String toString() {
        String name = null;
        if (this.getMethod() != null) {
            name = this.getMethod().getLocalVariableName(this.localVarArrIndex, this.getPos());
        }
        return "Ret to address in " + (name == null ? "#" + this.localVarArrIndex : name);
    }

    /**
     * Generates exactly one new state from the current state by performing the
     * ret operation represented by this instance.
     * @param state The old state
     * @return a list with exactly one successor state created by this
     * operation.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        // No need to refine
        final State newState = state.clone();

        //Get current stack frame:
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference ref = curFrame.getLocalVariable(this.localVarArrIndex);
        assert (ref instanceof ReturnAddress);
        final ReturnAddress ra = (ReturnAddress) ref;
        final OpCode target = ra.getOpCode();
        assert (target.getMethod().equals(curFrame.getMethod()));
        curFrame.setCurrentOpCode(target);

        return new Pair<State, EvaluationEdge>(newState, new EvaluationEdge());
    }

    /** {@inheritDoc} */
    @Override
    public final Set<OpCode> getAllPossibleSuccessors() {
        /*
         * The successor of this opcode is not known in our simple static
         * analysis, and we actually don't need it, as we trick around it
         * by adding both the following opcode *and* the target of a jsr.
         */
        return Collections.emptySet();
    }

    /** {@inheritDoc} */
    @Override
    public int getUsedLocalVariableIndex() {
        return this.localVarArrIndex;
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
