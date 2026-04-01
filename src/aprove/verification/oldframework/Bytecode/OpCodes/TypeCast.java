package aprove.verification.oldframework.Bytecode.OpCodes;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A class for the various typecast opcodes.
 * @author cotto
 */
public class TypeCast extends OpCode {
    /**
     * The type before conversion
     */
    private final OperandType fromType;

    /**
     * The type after conversion
     */
    private final OperandType toType;

    /**
     * Create a new typecast opcode
     * @param fromTypeParam the type before conversion
     * @param toTypeParam the type after conversion
     */
    public TypeCast(final OperandType fromTypeParam, final OperandType toTypeParam) {
        this.fromType = fromTypeParam;
        this.toType = toTypeParam;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "convert " + this.fromType + " to " + this.toType;
    }

    /**
     * @param ai Integer to cast
     * @return result of cast from Integer to Float
     */
    private AbstractFloat castFloat(final AbstractInt ai) {
        if (ai.isLiteral()) {
            final BigDecimal exactFloat = BigDecimal.valueOf(ai.getLiteral().longValue()).stripTrailingZeros();
            final BigDecimal convertedFloat =
                BigDecimal.valueOf((float) ai.getLiteral().longValue()).stripTrailingZeros();
            if (exactFloat.equals(convertedFloat)) {
                return AbstractFloat.create(ai.getLiteral().longValue());
            } else {
                return AbstractFloat.create();
            }
        } else {
            return AbstractFloat.create();
        }
    }

    /** {@inheritDoc} */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        final State clone = state.clone();
        final StackFrame sf = clone.getCurrentStackFrame();
        final AbstractVariableReference ref = sf.popOperandStack();
        final AbstractVariable av = clone.getAbstractVariable(ref);
        assert (av instanceof AbstractNumber);
        final AbstractNumber an = (AbstractNumber) av;
        final EvaluationEdge edge = new EvaluationEdge();
        final AbstractVariable newVar = this.getNewVar(an);
        AbstractVariableReference newRef = clone.createReferenceAndAdd(newVar, this.toType);
        if (an instanceof AbstractInt && newVar instanceof AbstractInt) {
            edge.add(new JBCIntegerRelation(newRef, IntegerRelationType.EQ, ref));
        }
        sf.pushOperandStack(newRef);
        clone.setCurrentOpCode(this.getNextOp());
        return new Pair<>(clone, edge);
    }

    /**
     * @param an the variable before the cast
     * @return a variable of the target type
     */
    private AbstractVariable getNewVar(final AbstractNumber an)
    {
        /*
         * TODO
         * The following 23 specific conversions on primitive types are called
         * the narrowing primitive conversions:
         *
         * byte to char
         * short to byte or char
         * char to byte or short
         * int to byte, short, or char
         * long to byte, short, char, or int
         * float to byte, short, char, int, or long
         * double to byte, short, char, int, long, or float
         *
         * Narrowing conversions may lose information about the overall
         * magnitude of a numeric value and may also lose precision.
         */
        AbstractInt ai = null;
        AbstractFloat af = null;
        switch (this.fromType) {
        case INTEGER:
            assert (an instanceof AbstractInt);
            ai = (AbstractInt) an;
            switch (this.toType) {
            case LONG:
            case BYTE:
            case SHORT:
            case CHAR:
                return ai;
            case FLOAT:
                return this.castFloat(ai);
            case DOUBLE:
                if (ai.isLiteral()) {
                    final BigDecimal exactDouble = BigDecimal.valueOf(ai.getLiteral().longValue()).stripTrailingZeros();
                    final BigDecimal convertedDouble =
                        BigDecimal.valueOf((double) ai.getLiteral().longValue()).stripTrailingZeros();
                    if (exactDouble.equals(convertedDouble)) {
                        return AbstractFloat.create(ai.getLiteral().longValue());
                    } else {
                        return AbstractFloat.create();
                    }
                } else {
                    return AbstractFloat.create();
                }
            default:
                assert (false);
                return null;
            }
        case LONG:
            assert (an instanceof AbstractInt);
            ai = (AbstractInt) an;
            switch (this.toType) {
            case INTEGER:
                return ai;
            case FLOAT:
                return this.castFloat(ai);
            case DOUBLE:
                if (ai.isLiteral()) {
                    final BigDecimal exactDouble = BigDecimal.valueOf(ai.getLiteral().longValue()).stripTrailingZeros();
                    final BigDecimal convertedDouble =
                        BigDecimal.valueOf((double) ai.getLiteral().longValue()).stripTrailingZeros();
                    if (exactDouble.equals(convertedDouble)) {
                        return AbstractFloat.create(ai.getLiteral().longValue());
                    } else {
                        return AbstractFloat.create();
                    }
                } else {
                    return AbstractFloat.create();
                }
            default:
                assert (false);
                return null;
            }
        case FLOAT:
            assert (an instanceof AbstractFloat);
            af = (AbstractFloat) an;
            switch (this.toType) {
            case INTEGER:
                if (af.isLiteral()) {
                    return AbstractInt.create((int) ((float) af.getLiteral()));
                } else {
                    return AbstractInt.getUnknown(IntegerType.UNBOUND);
                }
            case LONG:
                if (af.isLiteral()) {
                    return AbstractInt.create((long) ((float) af.getLiteral()));
                } else {
                    return AbstractInt.getUnknown(IntegerType.UNBOUND);
                }
            case DOUBLE:
                if (af.isLiteral()) {
                    return AbstractFloat.create((float) af.getLiteral());
                } else {
                    return AbstractFloat.create();
                }
            default:
                assert (false);
                return null;
            }
        case DOUBLE:
            assert (an instanceof AbstractFloat);
            af = (AbstractFloat) an;
            switch (this.toType) {
            case INTEGER:
                if (af.isLiteral()) {
                    return AbstractInt.create((int) af.getLiteral());
                } else {
                    return AbstractInt.getUnknown(IntegerType.UNBOUND);
                }
            case LONG:
                if (af.isLiteral()) {
                    return AbstractInt.create((long) af.getLiteral());
                } else {
                    return AbstractInt.getUnknown(IntegerType.UNBOUND);
                }
            case FLOAT:
                if (af.isLiteral()) {
                    return AbstractFloat.create((float) af.getLiteral());
                } else {
                    return AbstractFloat.create();
                }
            default:
                assert (false);
                return null;
            }
        default:
            assert (false);
            return null;
        }
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
