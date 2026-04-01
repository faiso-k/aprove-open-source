package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of store opcodes, which get values from the operand stack
 * and put them into the local variable array.
 * @author Marc Brockschmidt
 */
public final class Store extends OpCode implements LocalVariableUser {
    /**
     * Index in the local variable array where we store the value.
     */
    private final int localVarArrIndex;

    /**
     * Type of the variable to be stored.
     */
    private final OperandType opType;

    /**
     * @param type type of the value to be stored.
     * @param index position in the local variable array where we store the
     * value.
     */
    public Store(final OperandType type, final int index) {
        this.opType = type;
        this.localVarArrIndex = index;
    }

    /**
     * @return String representation of this {@link Store} opcode.
     */
    @Override
    public String toString() {
        String name = null;
        if (this.getMethod() != null) {
            /*
             * The name is only given starting at the next opcode, because the
             * variable just starts to exist.
             */
            int nextPos;
            if (this.getNextOp() != null) {
                nextPos = this.getNextOp().getPos();
            } else {
                nextPos = this.getPos();
            }
            name = this.getMethod().getLocalVariableName(this.localVarArrIndex, nextPos);
        }
        return "store " + this.opType + " to " + (name == null ? "#" + this.localVarArrIndex : name);
    }

    /**
     * Generates exactly one new state from the current state by performing the
     * store operation represented by this instance.
     * @param state The old state
     * @return a list with exact one successor state created by this operation.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        //Do we need to refine? No!
        final State newState = state.clone();

        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference ref = curFrame.popOperandStack();
        curFrame.setLocalVariable(this.localVarArrIndex, ref);

        curFrame.setCurrentOpCode(this.getNextOp());

        if (Globals.useAssertions) {
            final AbstractVariable av = newState.getAbstractVariable(ref);
            assert (this.opType.check(av)) : "Type of variable "
                + ref
                + " is "
                + av.getClass().getSimpleName()
                + ", value is "
                + av.toString()
                + ".\n We are trying to store it with opcode "
                + this.toString()
                + " (index "
                + this.localVarArrIndex
                + ") - Don't match!";
        }

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
        final StackFrame curAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();
        curInstFrame.setCurrentOpCode(curAbstrFrame.getCurrentOpCode());

        final AbstractVariableReference storedAbstrRef = preEval.getCurrentStackFrame().getOperandStack().peek(0);
        final AbstractVariableReference storedInstRef =
            State.mapOrCopyRef(preEval, preEvalInst, storedAbstrRef, refMap);
        curInstFrame.pushOperandStack(storedInstRef);

        if (this.getMethod().getActiveVariables(this.getPos()).contains(this.localVarArrIndex)) {
            curInstFrame
                .setLocalVariable(this.localVarArrIndex, State.mapOrCopyRef(
                    preEval,
                    preEvalInst,
                    curAbstrFrame.getLocalVariable(this.localVarArrIndex),
                    refMap));
        }

        this.handleActiveVarChangesInRevEv(preEval, preEvalInst, postEval, refMap);

        return preEvalInst;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        /*
         * This is a hack for LessLeaves.append(). There we have a tree t1 as argument. First we refine t1 != null. Then
         * we store t1 into another variable t. After that t is set to t.right until we reach t.right == null. When now
         * merging the first state with t1 ==  t1 with the state where t1.right == t, we get t1 -+><+- t. After a write
         * access to t we  do not have information about t anymore.
         *
         * To retain this information, we refine t1 before we save it to t.
         */
        final AbstractVariableReference storedRef = s.getCurrentStackFrame().getOperandStack().peek(0);
        if (!storedRef.pointsToInstance() || storedRef.isNULLRef()) {
            return false;
        }
        final AbstractVariableReference[] locVars = s.getCurrentStackFrame().getLocalVariables().getLocalVariables();
        final Collection<Integer> activeVars = s.getCurrentStackFrame().getActiveVariables();
        for (int index = 0; index < locVars.length; index++) {
            if (!activeVars.contains(index)) {
                continue;
            }
            final AbstractVariableReference locVar = locVars[index];
            if (storedRef.equals(locVar)) {
                if (!s.getHeapAnnotations().isMaybeExisting(storedRef)) {
                    final AbstractType at = s.getAbstractType(storedRef);
                    if (at.isConcrete()) {
                        if (!s.isFullyRealized(storedRef)) {
                            if (!s.getHeapAnnotations().getCyclicStructures().isCyclic(storedRef)) {
                                final TypeTree typeTree =
                                    s.getClassPath().getTypeTree(at.getMinimalClass().getMinimalClass());
                                return ObjectRefinement.forRealization(storedRef, typeTree, null, s, result, true)
                                    || ObjectRefinement.forEquality(storedRef, s, result);
                            }
                        }
                    }
                }
            }
        }
        return false;
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
