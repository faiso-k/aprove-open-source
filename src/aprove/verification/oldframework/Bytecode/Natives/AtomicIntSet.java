package aprove.verification.oldframework.Bytecode.Natives;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of setting functions in AtomicInteger. As we are not
 * able to handle multithreading anyway, all of them succeed and we can avoid
 * jumping through the shiny reflection hoops that are used in the original
 * Sun/Oracle implementation.
 *
 * @author Marc Brockschmidt
 */
public class AtomicIntSet extends PredefinedMethod {
    /**
     * The name of the class we are working on.
     */
    private static final ClassName ATOMIC_INTEGER_CN = ClassName
        .fromDotted("java.util.concurrent.atomic.AtomicInteger");

    /**
     * How many operand stack elements should be removed.
     */
    private final int popNumber;

    /**
     * The index of the new value.
     */
    private final int newValueIndex;

    /**
     * Indicates if we need to return anything (if yes, it's true::boolean)
     */
    private final boolean returnTrue;

    /**
     * Creates a new pseudo-method setting the atomic integer value.
     *
     * @param popMe how many operand stack elements should be removed
     * @param newValIdx the operand stack index (from the top) of the new value
     * @param retTrue indicates if we need to return anything (if yes, it's
     *  true::boolean)
     */
    public AtomicIntSet(final int popMe, final int newValIdx, final boolean retTrue) {
        this.popNumber = popMe;
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
        for (int i = 0; i < this.popNumber - 1; i++) {
            final AbstractVariableReference valRef = opStack.pop();
            if (i == this.newValueIndex) {
                newValRef = valRef;
            }
        }
        //instance is always the last ref:
        final AbstractVariableReference atomicIntRef = opStack.pop();
        final ObjectInstance atomicIntInst = (ObjectInstance) newState.getAbstractVariable(atomicIntRef);

        assert ((atomicIntInst instanceof AbstractInstance) || ((ConcreteInstance) atomicIntInst)
            .getMostSpecializedInstance()
            .getType()
            .getClassName()
            .equals(AtomicIntSet.ATOMIC_INTEGER_CN)) : "Trying to do AtomicInt magic on broken instance";

        //Set the field
        final Collection<DefiniteReachabilityAnnotationCreation> newDefReach =
            atomicIntInst.putField(newState, atomicIntRef, AtomicIntSet.ATOMIC_INTEGER_CN, "value", newValRef);

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
