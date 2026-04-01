package aprove.verification.oldframework.Bytecode.Natives;

import java.util.function.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the java.lang.String.intern() method. As we store no specific
 * string values, this just takes care of adding the needed Joins annotations.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class FreshStringReturn extends PredefinedMethod {
    /**
     * Specifies if the return value is marked as being non-null in all cases.
     */
    private final boolean alwaysExists;

    /**
     * How many operand stack elements should be removed.
     */
    private final int popNumber;

    private BiFunction<AbstractVariableReference, State, SizeRelationInformation> sizeRel;

    /**
     * Creates a new pseudo-method returning a fresh String.
     * @param popMe how many operand stack elements should be removed
     * @param alwaysEx specifies if the return value is marked as being non-null
     *  in all cases.
     */
    public FreshStringReturn(final int popMe, final boolean alwaysEx, BiFunction<AbstractVariableReference, State, SizeRelationInformation> sizeRel) {
        this.popNumber = popMe;
        this.alwaysExists = alwaysEx;
        this.sizeRel = sizeRel;
    }

    public FreshStringReturn(final int popMe, final boolean alwaysEx) {
        this(popMe, alwaysEx, null);
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State s) {
        final State newState = s.clone();

        final OperandStack opStack = newState.getCurrentStackFrame().getOperandStack();
        for (int i = 0; i < this.popNumber; i++) {
            opStack.pop();
        }

        final AbstractVariableReference stringRef = JLStringHelper.addAbstractStringToStateOrThrow(newState);

        if (stringRef == null) {
            return new Pair<>(newState, new EvaluationEdge());
        }

        if (this.alwaysExists) {
            newState.getHeapAnnotations().setExistenceIsKnown(stringRef);
        } else {
            newState.getHeapAnnotations().setMaybeExisting(stringRef);
        }

        // and push the result on the stack
        newState.getCurrentStackFrame().getOperandStack().push(stringRef);

        // and go to next opcode
        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());

        EvaluationEdge e = new EvaluationEdge();

        if (sizeRel != null) {
            e.add(sizeRel.apply(stringRef, s));
        }

        return new Pair<>(newState, e);
    }

}
