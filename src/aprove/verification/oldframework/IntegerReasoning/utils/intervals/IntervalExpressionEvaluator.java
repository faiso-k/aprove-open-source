package aprove.verification.oldframework.IntegerReasoning.utils.intervals;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

public class IntervalExpressionEvaluator extends FunctionalIntegerExpressionVisitor {

    private IntervalEvaluation evaluation;

    private final Stack<IntegerInterval> inferredBounds = new Stack<>();

    /**
     * @param expression Some expression
     * @param bounds Some bounds on variables
     * @return The interval that the given expression is guaranteed to be in.
     * Is never null.
     */
    public IntegerInterval evaluate(final FunctionalIntegerExpression expression, final IntervalEvaluation evaluation) {
        this.evaluation = evaluation;
        if (this.visit(expression)) {
            return this.inferredBounds.pop();
        } else {
            /* Since we only abort when we see an unsupported operation during the
             * *preorder*-traversal, we are sure that the stack is empty if we
             * aborted */
            return IntegerInterval.create(null, null);
        }
    }

    @Override
    public boolean visitAdditionPostorder(final CompoundFunctionalIntegerExpression addition) {
        final IntegerInterval rhsSummand = this.inferredBounds.pop();
        final IntegerInterval lhsSummand = this.inferredBounds.pop();

        this.inferredBounds.push(lhsSummand.add(rhsSummand));

        return true;
    }

    @Override
    public boolean visitConjunctionPostorder(final CompoundFunctionalIntegerExpression conjunction) {
        return false;
    }

    @Override
    public boolean visitConstRef(final IntegerConstant constRef) {
        this.inferredBounds.push(IntegerInterval.createLiteral(constRef.getIntegerValue()));
        return true;
    }

    @Override
    public boolean visitDisjunctionPreorder(final CompoundFunctionalIntegerExpression disjunction) {
        return false;
    }

    @Override
    public boolean visitDivisionPreorder(final CompoundFunctionalIntegerExpression division) {
        return false;
    }

    @Override
    public boolean visitModuloPreorder(CompoundFunctionalIntegerExpression CompoundFunctionalIntegerExpression) {
        return false;
    }

    @Override
    public boolean visitMultiplicationPostorder(final CompoundFunctionalIntegerExpression multiplication) {
        final IntegerInterval rhsMultiplicand = this.inferredBounds.pop();
        final IntegerInterval lhsMultiplicand = this.inferredBounds.pop();

        this.inferredBounds.push(lhsMultiplicand.multiply(rhsMultiplicand));

        return true;
    }

    @Override
    public boolean visitNegationPreorder(final CompoundFunctionalIntegerExpression negation) {
        return false;
    }

    @Override
    public boolean visitPowerPreorder(final CompoundFunctionalIntegerExpression power) {
        return false;
    }

    @Override
    public boolean visitRemainderPreorder(final CompoundFunctionalIntegerExpression remainder) {
        return false;
    }

    @Override
    public boolean visitShiftLeftPreorder(final CompoundFunctionalIntegerExpression shift) {
        return false;
    }

    @Override
    public boolean visitShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        return false;
    }

    @Override
    public boolean visitSubtractionPostorder(final CompoundFunctionalIntegerExpression subtraction) {
        final IntegerInterval subtrahend = this.inferredBounds.pop();
        final IntegerInterval minuend = this.inferredBounds.pop();

        this.inferredBounds.push(minuend.subtract(subtrahend));

        return true;
    }

    @Override
    public boolean visitUnsignedShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        return false;
    }

    @Override
    public boolean visitVarRef(final IntegerVariable varRef) {
        this.inferredBounds.push(this.evaluation.getInterval(varRef));
        return true;
    }

    @Override
    public boolean visitXorPreorder(final CompoundFunctionalIntegerExpression xor) {
        return false;
    }

}
