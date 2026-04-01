/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.OpCodes;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of arithmetic operations on abstract float variables.
 */
public class FloatArithmetic extends OpCode {
    /**
     * Possible arithmetic operators.
     */
    public static enum FloatArithType {
        /**
         * Addition.
         */
        ADD("+"),

        /**
         * Subtraction.
         */
        SUB("-"),

        /**
         * Multiplication.
         */
        MUL("*"),

        /**
         * Division.
         */
        DIV("/"),

        /**
         * Remainder of division.
         */
        REM("%"),

        /**
         * Negate.
         */
        NEG("-");

        /**
         * A short string representation.
         */
        private String string;

        /**
         * @param stringParam a short string representation
         */
        FloatArithType(final String stringParam) {
            this.string = stringParam;
        }

        /**
         * @return a short string representation
         */
        @Override
        public String toString() {
            return this.string;
        }

        /**
         * @return a long string representation
         */
        public String toLongString() {
            return super.toString();
        }
    }

    /**
     * Type of arithmetic operation represented by this instance.
     */
    private final FloatArithType operationType;

    /**
     * Construct a new instance representing the documented operation.
     * @param opType type of arithmetic operation
     */
    public FloatArithmetic(final FloatArithType opType) {
        this.operationType = opType;
    }

    /** {@inheritDoc} */
    @Override
    public final String toString() {
        return this.operationType.toLongString();
    }

    /** {@inheritDoc} */
    @Override
    public final Pair<State, EvaluationEdge> evaluate(final State state) {
        final State newState = state.clone();

        //Get data:
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference opBR = curFrame.popOperandStack();
        assert (newState.getAbstractVariable(opBR) instanceof AbstractFloat);
        final AbstractFloat opB = (AbstractFloat) newState.getAbstractVariable(opBR);

        AbstractVariableReference opAR = null;
        AbstractFloat opA = null;
        final boolean sameReference;
        AbstractFloat res = null;
        final AbstractVariableReference resR;

        if (this.operationType == FloatArithType.NEG) {
            //NEG only needs one value
            res = opB.negate();
            resR = newState.createReferenceAndAdd(res, opBR.getPrimitiveType());
        } else {
            opAR = curFrame.popOperandStack();
            assert (newState.getAbstractVariable(opAR) instanceof AbstractFloat);
            opA = (AbstractFloat) newState.getAbstractVariable(opAR);
            sameReference = opAR.equals(opBR);
            final boolean isFPStrict = curFrame.getMethod().isStrictFP();
            switch (this.operationType) {
            case ADD:
                res = opA.add(opB, isFPStrict);
                break;
            case DIV:
                res = opA.div(opB, sameReference, isFPStrict);
                break;
            case MUL:
                res = opA.mul(opB, isFPStrict);
                break;
            case REM:
                res = opA.rem(opB, sameReference, isFPStrict);
                break;
            case SUB:
                res = opA.sub(opB, sameReference, isFPStrict);
                break;
            default:
                assert (false) : "Unknown operation on floats";
            }
            resR = newState.createReferenceAndAdd(res, opAR.getPrimitiveType());
        }

        assert (res != null) : "There has to be a result for an arithmetic expression";

        curFrame.pushOperandStack(resR);

        curFrame.setCurrentOpCode(this.getNextOp());

        final EvaluationEdge info = new EvaluationEdge();
        if (opA == null || !(opA.isLiteral() && opB.isLiteral())) {
            info.add(new FloatResultInformation(opAR, this.operationType, opBR, resR));
        }
        return new Pair<State, EvaluationEdge>(newState, info);
    }

    @Override
    public int getNumberOfArguments() {
        switch (operationType) {
            case NEG: return 1;
            default: return 2;
        }
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
