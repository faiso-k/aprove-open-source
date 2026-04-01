package aprove.verification.oldframework.IntegerReasoning.constants;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Decides the truth value of a relation that only has constants on both sides
 * @author Alexander Weinert
 */
class ConstantRelationAnalyzer extends IntegerRelationVisitor {
    final ConstantExpressionEvaluator evaluator = new ConstantExpressionEvaluator();

    Boolean result = null;
    BigInteger lhsResult = null;
    BigInteger rhsResult = null;

    /**
     * @param relation Some relation
     * @return YES, if the relation contains only constants and is true.
     * NO, if it contains only constants and is false. MAYBE if it contains
     * not only constants
     */
    public boolean decide(final IntegerRelation relation) {
        this.visit(relation);
        final Boolean returnValue = this.result;
        this.result = null;
        if (returnValue == null) {
            return false;
        }
        return returnValue;
    }

    @Override
    public boolean visitRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.lhsResult = this.evaluator.evaluate(lhs);
        if (this.lhsResult == null) {
            return false;
        }
        this.rhsResult = this.evaluator.evaluate(rhs);
        if (this.rhsResult == null) {
            return false;
        }
        return true;
    }

    @Override
    public void visitEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = (this.lhsResult.compareTo(this.rhsResult) == 0);
    }

    @Override
    public void visitNotEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = (this.lhsResult.compareTo(this.rhsResult) != 0);
    }

    @Override
    public void visitLessThanRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = (this.lhsResult.compareTo(this.rhsResult) < 0);
    }

    @Override
    public void visitLessThanEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = (this.lhsResult.compareTo(this.rhsResult) <= 0);
    }

}
