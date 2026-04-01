package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AtomicFieldUpdaterInfo.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of setting functions in AtomicReferenceFieldUpdaterImpl. As we
 * are not able to handle multithreading anyway, all of them succeed and we can
 * avoid jumping through the shiny reflection hoops that are used in the original
 * Sun/Oracle implementation.
 *
 * @author Marc Brockschmidt
 */
public class AtomicReferenceFieldSet extends PredefinedMethod {
    /**
     * How many operand stack elements should be removed.
     */
    private final int popNumber;

    /**
     * The index of the instance to update.
     */
    private final int changedInstIndex;

    /**
     * The index of the new value.
     */
    private final int newValueIndex;

    /**
     * Indicates if we need to return anything (if yes, it's true::boolean)
     */
    private final boolean returnTrue;

    /**
     * Creates a new pseudo-method updating a field.
     *
     * @param popMe how many operand stack elements should be removed.
     * @param changedInstIdx the operand stack index (from the top) of the
     *  instance to update.
     * @param newValIdx the operand stack index (from the top) of the new value.
     * @param retTrue indicates if we need to return anything (if yes, it's
     *  true::boolean).
     */
    public AtomicReferenceFieldSet(final int popMe, final int changedInstIdx, final int newValIdx, final boolean retTrue)
    {
        this.popNumber = popMe;
        this.changedInstIndex = changedInstIdx;
        this.newValueIndex = newValIdx;
        this.returnTrue = retTrue;
        assert (this.popNumber > this.newValueIndex) : "We expect the new value as argument!";
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();
        final OperandStack opStack = newState.getCurrentStackFrame().getOperandStack();
        AbstractVariableReference newValRef = null;
        AbstractVariableReference instToUpdateRef = null;

        for (int i = 0; i < this.popNumber - 1; i++) {
            final AbstractVariableReference valRef = opStack.pop();
            if (i == this.newValueIndex) {
                newValRef = valRef;
            }
            if (i == this.changedInstIndex) {
                instToUpdateRef = valRef;
            }
        }
        //Get the updater ref, it's always at the bottom:
        final AbstractVariableReference updaterRef = opStack.pop();
        final ObjectInstance instToUpdate = (ObjectInstance) newState.getAbstractVariable(instToUpdateRef);
        final AtomicFieldUpdaterData updaterData = newState.getAtomicFieldUpdaterInfo().get(updaterRef);

        assert (newValRef != null && instToUpdateRef != null && updaterRef != null) : "Trying to use atomic reference field updater, but miss information";

        //Set the field
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach =
            instToUpdate.putField(
                newState,
                instToUpdateRef,
                updaterData.getInstanceType().getMinimalClass(),
                updaterData.getFieldName(),
                newValRef);

        //Return true (i.e., the int of value 1), if needed
        if (this.returnTrue) {
            opStack.push(newState.createReferenceAndAdd(AbstractInt.getOne(), OperandType.INTEGER));
        }

        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());
        final EvaluationEdge edge = new EvaluationEdge();
        edge.addAll(newDefReach);
        return new Pair<>(newState, edge);
    }

}
