package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Creates LLVMTerms.
 * @author Alexander Weinert, cryingshadow
 */
public interface LLVMTermFactory {

    /**
     * @param exp Some functional integer expression.
     * @param termFactory Some term factory.
     * @return An LLVMTerm representing the specified functional integer expression.
     * @throws IllegalArgumentException If the specified expression cannot be transformed into an LLVMTerm by the
     *                                  specified factory.
     */
    public static LLVMTerm create(FunctionalIntegerExpression exp, LLVMTermFactory termFactory)
    throws IllegalArgumentException {
        if (exp instanceof LLVMTerm) {
            return (LLVMTerm)exp;
        }
        if (exp instanceof IntegerConstant) {
            return termFactory.constant(((IntegerConstant)exp).getIntegerValue());
        }
        if (exp instanceof BinaryExpression && exp instanceof IntegerFunctionExpression) {
            ArithmeticOperationType type =
                ArithmeticOperationType.forFunctionSymbol(((IntegerFunctionExpression)exp).getRootSymbol());
            if (type != null) {
                BinaryExpression bin = (BinaryExpression)exp;
                return
                    termFactory.operation(
                        type,
                        termFactory.create((FunctionalIntegerExpression)bin.getLhs()),
                        termFactory.create((FunctionalIntegerExpression)bin.getRhs())
                    );
            }
        } else if (exp instanceof Variable) {
            return termFactory.varRef(exp.getName());
        }
        throw new IllegalArgumentException("Cannot transform " + exp + " to an LLVMTerm!");
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing lhs + rhs.
     */
    default LLVMTerm add(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.ADD, lhs, rhs);
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing lhs & rhs.
     */
    default LLVMTerm and(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.AND, lhs, rhs);
    }

    /**
     * @param value The value.
     * @return A constant with the specified value.
     */
    default LLVMConstant constant(BigInteger value) {
        if (BigInteger.ZERO.compareTo(value) == 0) {
            return this.zero();
        }
        if (BigInteger.ONE.compareTo(value) == 0) {
            return this.one();
        }
        if (IntegerUtils.NEGONE.compareTo(value) == 0) {
            return this.negone();
        }
        return LLVMDefaultConstant.create(value);
    }

    /**
     * @param value The value.
     * @return A constant with the specified value.
     */
    default LLVMConstant constant(long value) {
        return this.constant(BigInteger.valueOf(value));
    }

    /**
     * @param value The value.
     * @return A constant with the specified value.
     */
    default LLVMConstant constant(double value) {
        return LLVMDoubleConstant.create(value);
    }

    /**
     * @param value The value.
     * @return A constant with the specified value.
     */
    default LLVMConstant constant(float value) {
        return LLVMFloatConstant.create(value);
    }

    /**
     * @param exp Some functional integer expression.
     * @return An LLVMTerm representing the specified functional integer expression.
     * @throws IllegalArgumentException If the specified expression cannot be transformed into an LLVMTerm.
     */
    default LLVMTerm create(FunctionalIntegerExpression exp) throws IllegalArgumentException {
        return LLVMTermFactory.create(exp, this);
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing lhs / rhs (truncating integer division).
     */
    default LLVMTerm tidiv(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.TIDIV, lhs, rhs);
    }

    /**
     * @return A fresh symbolic variable.
     */
    default LLVMSymbolicVariable freshVariable() {
        return new LLVMSymbolicVariable(UIDGenerator.getValueUIDGenerator().next());
    }

    /**
     * @param dName The debug name.
     * @return A fresh symbolic variable.
     */
    default LLVMSymbolicVariable freshVariable(String dName) {
        return new LLVMSymbolicVariable(UIDGenerator.getValueUIDGenerator().next(), dName);
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing lhs * rhs.
     */
    default LLVMTerm mult(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.MUL, lhs, rhs);
    }

    /**
     * @return The constant -1.
     */
    LLVMConstant negone();

    /**
     * @return The constant 1.
     */
    LLVMConstant one();

    /**
     * @param type The arithmetic operation.
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing the specified operation (lhs type rhs).
     */
    default LLVMTerm operation(ArithmeticOperationType type, LLVMTerm lhs, LLVMTerm rhs) {
        switch (type) {
            case ADD:
                if (
                    lhs instanceof LLVMConstant && ((LLVMConstant)lhs).getIntegerValue().compareTo(BigInteger.ZERO) == 0
                ) {
                    return rhs;
                }
                // fall-through
            case SUB:
                if (
                    rhs instanceof LLVMConstant && ((LLVMConstant)rhs).getIntegerValue().compareTo(BigInteger.ZERO) == 0
                ) {
                    return lhs;
                }
                break;
            case MUL:
                if (
                    lhs instanceof LLVMConstant && ((LLVMConstant)lhs).getIntegerValue().compareTo(BigInteger.ONE) == 0
                ) {
                    return rhs;
                }
                // fall-through
            case TIDIV:
                if (
                    rhs instanceof LLVMConstant && ((LLVMConstant)rhs).getIntegerValue().compareTo(BigInteger.ONE) == 0
                ) {
                    return lhs;
                }
                break;
            default:
                // do nothing
        }
        return new LLVMOperation(type, lhs, rhs);
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A term representing lhs - rhs.
     */
    default LLVMTerm sub(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.SUB, lhs, rhs);
    }

    /**
     * @param name The name.
     * @return A variable with the specified name.
     */
    default LLVMSymbolicVariable varRef(String name) {
        return new LLVMSymbolicVariable(name);
    }

    /**
     * @param name The name.
     * @param dName The debug name.
     * @return A variable with the specified name.
     */
    default LLVMSymbolicVariable varRef(String name, String dName) {
        return new LLVMSymbolicVariable(name, dName);
    }

    /**
     * @return The constant 0.
     */
    LLVMConstant zero();

}
