package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Represents a binary operation like add, and, subtract, multiply, ...
 * @author Jera Hensel
 */
public class LLVMLiteralOperation implements LLVMLiteralExpression, BinaryIntegerFunctionExpression {

    /**
     * Creates an operation.
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     * @return The operation.
     */
    public static LLVMLiteralOperation create(
        ArithmeticOperationType op,
        LLVMLiteralExpression l,
        LLVMLiteralExpression r
    ) {
        return new LLVMLiteralOperation(op, l, r);
    }

    /**
     * Left-hand side of this (binary) operation. Never null.
     */
    private final LLVMLiteralExpression lhs;

    /**
     * Type of the (binary) operation. Never null.
     */
    private final ArithmeticOperationType opType;

    /**
     * Right-hand side of this (binary) operation. Never null.
     */
    private final LLVMLiteralExpression rhs;

    /**
     * Creates an operation.
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     */
    private LLVMLiteralOperation(ArithmeticOperationType op, LLVMLiteralExpression l, LLVMLiteralExpression r) {
        if (Globals.useAssertions) {
            assert (op != null) : "OperationType must not be null!";
            assert (l != null && r != null) : "Arguments must not be null!";
        }
        this.lhs = l;
        this.rhs = r;
        this.opType = op;
    }

    @Override
    public LLVMLiteralOperation applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return (LLVMLiteralOperation)this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMLiteralOperation) {
            LLVMLiteralOperation other = (LLVMLiteralOperation) o;
            if (this.opType != other.opType) {
                return false;
            }
            // note that both sides must be non-null
            return (this.lhs.equals(other.lhs) && this.rhs.equals(other.rhs))
                || (this.opType.isCommutative() && this.lhs.equals(other.rhs) && this.rhs.equals(other.lhs));
        } else {
            return false;
        }
    }

    @Override
    public BigInteger evaluate() {
        switch (this.getOperation()) {
            case ADD:
                return this.getLhs().evaluate().add(this.getRhs().evaluate());
            case SUB:
                return this.getLhs().evaluate().subtract(this.getRhs().evaluate());
            case MUL:
                return this.getLhs().evaluate().multiply(this.getRhs().evaluate());
            default:
                // not needed (yet)
        }
        return null;
    }

    @Override
    public BigInteger evaluate(Map<LLVMLiteral, BigInteger> varToVal) {
        switch (this.getOperation()) {
            case ADD:
                return this.getLhs().evaluate(varToVal).add(this.getRhs().evaluate(varToVal));
            case SUB:
                return this.getLhs().evaluate(varToVal).subtract(this.getRhs().evaluate(varToVal));
            case MUL:
                return this.getLhs().evaluate(varToVal).multiply(this.getRhs().evaluate(varToVal));
            default:
                // not needed (yet)
        }
        return null;
    }

    @Override
    public LLVMLiteralExpression getLhs() {
        return this.lhs;
    }

    @Override
    public ArithmeticOperationType getOperation() {
        return this.opType;
    }

    @Override
    public LLVMLiteralExpression getRhs() {
        return this.rhs;
    }

    @Override
    @SuppressWarnings("unchecked")
    public Set<LLVMVariableLiteral> getVariables() {
        return (Set<LLVMVariableLiteral>)CompoundExpression.getVariables(this);
    }

    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result =
            prime
            * result
            + ((this.getLhs() == null) ? 0 : this.getLhs().hashCode())
            + ((this.getRhs() == null) ? 0 : this.getRhs().hashCode());
        result = prime * result + ((this.getOperation() == null) ? 0 : this.getOperation().ordinal());
        return result;
    }

    @Override
    public LLVMLiteralOperation negate() {
        return LLVMLiteralOperation.create(ArithmeticOperationType.MUL, new LLVMRegularIntLiteral(32, -1, false), this);
    }

    @Override
    public LLVMLiteralOperation setLhs(Expression lhs) {
        return LLVMLiteralOperation.create(this.getOperation(), (LLVMLiteralExpression)lhs, this.getRhs());
    }

    @Override
    public LLVMLiteralOperation setRhs(Expression rhs) {
        return LLVMLiteralOperation.create(this.getOperation(), this.getLhs(), (LLVMLiteralExpression)rhs);
    }

    @Override
    public LLVMLiteralExpression substitute(Map<LLVMLiteral, ? extends LLVMLiteral> substitution) {
        return
            LLVMLiteralOperation.create(
                this.getOperation(),
                this.getLhs().substitute(substitution),
                this.getRhs().substitute(substitution)
            );
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.lhs.toString());
        res.append(" ");
        res.append(this.getOperation());
        res.append(" ");
        res.append(this.rhs.toString());
        return res.toString();
    }

    @Override
    public LLVMHeuristicTerm transformToLLVMHeuristicTerm(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicTermFactory factory
    ) {
        LLVMTerm left = this.getLhs().transformToLLVMHeuristicTerm(varToRef, factory);
        LLVMTerm right = this.getRhs().transformToLLVMHeuristicTerm(varToRef, factory);
        if (left != null && right != null) {
            return factory.operation(this.opType, left, right);
        } else {
            return null;
        }
    }

}
