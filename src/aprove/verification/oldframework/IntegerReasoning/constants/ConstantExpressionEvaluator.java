package aprove.verification.oldframework.IntegerReasoning.constants;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

public class ConstantExpressionEvaluator extends FunctionalIntegerExpressionVisitor {
    final Stack<BigInteger> evaluationStack = new Stack<>();

    public BigInteger evaluate(final FunctionalIntegerExpression expression) {
        if (this.visit(expression)) {
            return this.evaluationStack.pop();
        } else {
            this.evaluationStack.clear();
            return null;
        }
    }

    @Override
    public boolean visitConstRef(final IntegerConstant constRef) {
        this.evaluationStack.push(constRef.getIntegerValue());
        return true;
    }

    @Override
    public boolean visitVarRef(final IntegerVariable varRef) {
        // We do not handle variables, so abort traversal
        return false;
    }

    @Override
    public boolean visitAdditionPostorder(final CompoundFunctionalIntegerExpression addition) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.add(rhs));
        return true;
    }

    @Override
    public boolean visitConjunctionPostorder(final CompoundFunctionalIntegerExpression conjunction) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.and(rhs));
        return true;
    }

    @Override
    public boolean visitDivisionPostorder(final CompoundFunctionalIntegerExpression division) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.divide(rhs));
        return true;
    }

    @Override
    public boolean visitMultiplicationPostorder(final CompoundFunctionalIntegerExpression multiplication) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.multiply(rhs));
        return true;
    }

    @Override
    public boolean visitNegationPostorder(final CompoundFunctionalIntegerExpression negation) {
        final BigInteger rhs = this.evaluationStack.pop();

        this.evaluationStack.push(rhs.negate());
        return true;
    }

    @Override
    public boolean visitDisjunctionPostorder(final CompoundFunctionalIntegerExpression disjunction) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.or(rhs));
        return true;
    }

    @Override
    public boolean visitPowerPostorder(final CompoundFunctionalIntegerExpression power) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.pow(rhs.intValue()));
        return true;
    }

    @Override
    public boolean visitRemainderPostorder(final CompoundFunctionalIntegerExpression remainder) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.remainder(rhs));
        return true;
    }

    @Override
    public boolean visitShiftLeftPostorder(final CompoundFunctionalIntegerExpression shift) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.shiftLeft(rhs.intValue()));
        return true;
    }

    @Override
    public boolean visitShiftRightPostorder(final CompoundFunctionalIntegerExpression shift) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.shiftRight(rhs.intValue()));
        return true;
    }

    @Override
    public boolean visitUnsignedShiftRightPostorder(final CompoundFunctionalIntegerExpression shift) {
        // We do not support an unsigned shift right now
        return true;
    }

    @Override
    public boolean visitSubtractionPostorder(final CompoundFunctionalIntegerExpression subtraction) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.subtract(rhs));
        return true;
    }

    @Override
    public boolean visitXorPostorder(final CompoundFunctionalIntegerExpression xor) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.xor(rhs));
        return true;
    }

    @Override
    public boolean visitModuloPostorder(final CompoundFunctionalIntegerExpression mod) {
        final BigInteger rhs = this.evaluationStack.pop();
        final BigInteger lhs = this.evaluationStack.pop();

        this.evaluationStack.push(lhs.mod(rhs));
        return true;
    }
}
