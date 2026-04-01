package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of increment opcodes.
 * @author Marc Brockschmidt
 */
public final class Inc extends OpCode implements LocalVariableUser {
    /**
     * Integer value to be added in the increment operation.
     */
    private final int constToBeAdded;

    /**
     * Index in the local variable array of the variable to be incremented.
     */
    private final int localVarArrIndex;

    /**
     * @param index local variable array index of the variable to be incremented.
     * @param value value to be added in the increment operation.
     */
    public Inc(final int index, final int value) {
        this.constToBeAdded = value;
        this.localVarArrIndex = index;
    }

    /**
     * Generates exactly one new state from the current state by performing the
     * increment operation represented by this instance.
     * @param state The old state
     * @return a list with exact one successor state created by this operation.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        //Do we need to refine? No!
        final State newState = state.clone();

        //Get data:
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference oldValRef = curFrame.getLocalVariable(this.localVarArrIndex);
        final AbstractInt oldVal = (AbstractInt) newState.getAbstractVariable(oldValRef);
        final LiteralInt inc = AbstractInt.create(this.constToBeAdded);
        AbstractNumber res =  oldVal.add(inc, IntegerType.JAVA_INT);
        final AbstractVariableReference resRef = newState.createReferenceAndAdd(res, OperandType.INTEGER);
        curFrame.setLocalVariable(this.localVarArrIndex, resRef);

        curFrame.setCurrentOpCode(this.getNextOp());

        newState.getIntegerRelations().noteNewRefInRelation(resRef, oldValRef, this.constToBeAdded);
        final EvaluationEdge info = new EvaluationEdge();
        if (!oldVal.isLiteral()) {
            info.add(new IntegerResultInformation(oldValRef, ArithmeticOperationType.ADD, inc, resRef));
        }
        return new Pair<>(newState, info);
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
        final StackFrame curAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();
        curInstFrame.setCurrentOpCode(curAbstrFrame.getCurrentOpCode());

        //First check if we know the value of the old value and used that, if possible;
        final AbstractVariableReference abstrOldValRef = curAbstrFrame.getLocalVariable(this.localVarArrIndex);
        final AbstractVariableReference instOldValRef;
        if (refMap.containsKey(abstrOldValRef)) {
            instOldValRef = refMap.get(abstrOldValRef);
        } else {
            final AbstractVariableReference newValRef = curInstFrame.getLocalVariable(this.localVarArrIndex);
            final AbstractInt newVal = (AbstractInt) postEvalInst.getAbstractVariable(newValRef);
            final AbstractInt inc = AbstractInt.create(this.constToBeAdded);
            AbstractNumber oldVal = newVal.add(inc.negate(IntegerType.UNBOUND), IntegerType.UNBOUND);
            instOldValRef = preEvalInst.createReferenceAndAdd(oldVal, OperandType.INTEGER);
        }

        curInstFrame.setLocalVariable(this.localVarArrIndex, instOldValRef);
        return preEvalInst;
    }

    /**
     * @return String representation of this {@link Inc} opcode.
     */
    @Override
    public String toString() {
        String name = null;
        if (this.getMethod() != null) {
            name = this.getMethod().getLocalVariableName(this.localVarArrIndex, this.getPos());
        }
        if (name == null) {
            name = "#" + this.localVarArrIndex;
        }

        return "increment " + name + " by " + this.constToBeAdded;
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
