package aprove.verification.oldframework.IntegerReasoning.utils.intervals;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;

public class IntervalRelationSolver extends IntegerRelationVisitor {

    final private IntervalExpressionEvaluator evaluator = new IntervalExpressionEvaluator();

    private IntervalEvaluation evaluation = null;
    private IntegerInterval lhsInterval, rhsInterval;
    private YNM result = null;

    public YNM decide(final IntegerRelation relation, final IntervalEvaluation evaluation) {
        this.evaluation = evaluation;
        this.visit(relation);
        this.lhsInterval = null;
        this.rhsInterval = null;
        final YNM returnValue = this.result;
        this.result = null;
        return returnValue;
    }

    @Override
    public boolean visitRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.lhsInterval = this.evaluator.evaluate(lhs, this.evaluation);
        this.rhsInterval = this.evaluator.evaluate(rhs, this.evaluation);
        return true;
    }

    @Override
    public void visitEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        if (this.lhsInterval.canInferEquals(this.rhsInterval)) {
            this.result = YNM.YES;
        } else if (this.lhsInterval.canInferUnequals(this.rhsInterval)) {
            this.result = YNM.NO;
        } else {
            this.result = YNM.MAYBE;
        }
    }

    @Override
    public void visitNotEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        if (this.lhsInterval.canInferUnequals(this.rhsInterval)) {
            this.result = YNM.YES;
        } else if (this.lhsInterval.canInferEquals(this.rhsInterval)) {
            this.result = YNM.NO;
        } else {
            this.result = YNM.MAYBE;
        }
    }

    @Override
    public void visitLessThanRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        if (this.lhsInterval.canInferLessThan(this.rhsInterval)) {
            this.result = YNM.YES;
        } else if (this.rhsInterval.canInferLessThanEquals(this.lhsInterval)) {
            this.result = YNM.NO;
        } else {
            this.result = YNM.MAYBE;
        }
    }

    @Override
    public void visitLessThanEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        if (this.lhsInterval.canInferLessThanEquals(this.rhsInterval)) {
            this.result = YNM.YES;
        } else if (this.rhsInterval.canInferLessThan(this.lhsInterval)) {
            this.result = YNM.NO;
        } else {
            this.result = YNM.MAYBE;
        }
    }

}
