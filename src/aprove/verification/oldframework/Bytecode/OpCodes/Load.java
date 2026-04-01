package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of load opcodes, which get values from the local variable
 * array and put them on the operand stack (<code>Tload</code>,
 * <code>Tload_n</code>).
 * <p>
 * For loading from arrays (<code>Taload</code>) see {@link ArrayAccess}.
 * </p>
 * @author Marc Brockschmidt
 */
public final class Load extends OpCode implements LocalVariableUser {
    /**
     * Index in the local variable array of the variable to be loaded.
     */
    private final int localVarArrIndex;

    /**
     * Type of the variable to be loaded.
     */
    private final OperandType opType;

    /**
     * @param type type of the value to be loaded.
     * @param index position in the local variable to load from.
     */
    public Load(final OperandType type, final int index) {
        this.opType = type;
        this.localVarArrIndex = index;
    }

    /**
     * @return String representation of this {@link Load} opcode.
     */
    @Override
    public String toString() {
        String name = null;
        if (this.getMethod() != null) {
            name = this.getMethod().getLocalVariableName(this.localVarArrIndex, this.getPos());
        }
        return "load " + this.opType + " " + (name == null ? "#" + this.localVarArrIndex : name);
    }

    /**
     * Generates exactly one new state from the current state by performing the
     * load operation represented by this instance.
     *
     * @param curState The old state
     * @return the successor state created by this operation.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State curState) {
        //Do we need to refine? No!
        final State newState = curState.clone();

        //Get current stack frame:
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference ref = curFrame.getLocalVariable(this.localVarArrIndex);

        if (Globals.useAssertions) {
            assert (ref != null) : "Loading from local variable array failed: Register "
                + this.localVarArrIndex
                + " empty";
            assert (this.opType != OperandType.ADDRESS || !(ref instanceof ReturnAddress)) : "The aload* opcodes may not be used to load returnAddresses (cf JVMS)";
            final AbstractVariable av = newState.getAbstractVariable(ref);
            assert (this.opType.check(av)) : "Type of variable "
                + ref
                + " is "
                + av.getClass().getSimpleName()
                + ", value is "
                + av.toString()
                + ".\n We are trying to load it with opcode "
                + this.toString()
                + " (index "
                + this.localVarArrIndex
                + ") - Don't match!";
        }
        curFrame.pushOperandStack(ref);

        curFrame.setCurrentOpCode(this.getNextOp());

        return new Pair<State, EvaluationEdge>(newState, new EvaluationEdge());
    }

    /** {@inheritDoc} */
    @Override
    public int getUsedLocalVariableIndex() {
        return this.localVarArrIndex;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();

        /* Un-Load one element (it was copied from a local variable to the
         * stack)
         */
        curInstFrame.popOperandStack();
        curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        this.handleActiveVarChangesInRevEv(preEval, preEvalInst, postEval, refMap);

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return 0;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
