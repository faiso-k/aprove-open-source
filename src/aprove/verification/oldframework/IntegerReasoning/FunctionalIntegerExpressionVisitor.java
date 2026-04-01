package aprove.verification.oldframework.IntegerReasoning;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

public abstract class FunctionalIntegerExpressionVisitor implements Visitor<Expression, Expression> {

    @Override
    public Expression visit(Expression v) {
        if (v instanceof IntegerConstant) {
            return this.visitConstRef((IntegerConstant)v) ? v : null;
        } else if (v instanceof IntegerVariable) {
            return this.visitVarRef((IntegerVariable)v) ? v : null;
        } else if (v instanceof CompoundFunctionalIntegerExpression) {
            CompoundFunctionalIntegerExpression exp = (CompoundFunctionalIntegerExpression)v;
            if (!this.callPreorderHook(exp)) {
                return null;
            }
            for (FunctionalIntegerExpression arg : exp.getArguments()) {
                if (arg.accept(this) == null) {
                    return null;
                }
            }
            return this.callPostorderHook(exp) ? v : null;
        }
        return v;
    }

    public boolean visitAdditionInorder(final CompoundFunctionalIntegerExpression addition) {
        return true;
    }

    public boolean visitAdditionPostorder(final CompoundFunctionalIntegerExpression addition) {
        return true;
    }

    public boolean visitAdditionPreorder(final CompoundFunctionalIntegerExpression addition) {
        return true;
    }

    public boolean visitConjunctionInorder(final CompoundFunctionalIntegerExpression conjunction) {
        return true;
    }

    public boolean visitConjunctionPostorder(final CompoundFunctionalIntegerExpression conjunction) {
        return true;
    }

    public boolean visitConjunctionPreorder(final CompoundFunctionalIntegerExpression conjunction) {
        return true;
    }

    public boolean visitConstRef(final IntegerConstant constRef) {
        return true;
    }

    public boolean visitDisjunctionInorder(final CompoundFunctionalIntegerExpression disjunction) {
        return true;
    }

    public boolean visitDisjunctionPostorder(final CompoundFunctionalIntegerExpression disjunction) {
        return true;
    }

    public boolean visitDisjunctionPreorder(final CompoundFunctionalIntegerExpression disjunction) {
        return true;
    }

    public boolean visitDivisionInorder(final CompoundFunctionalIntegerExpression division) {
        return true;
    }

    public boolean visitDivisionPostorder(final CompoundFunctionalIntegerExpression division) {
        return true;
    }

    public boolean visitDivisionPreorder(final CompoundFunctionalIntegerExpression division) {
        return true;
    }

    public boolean visitModuloInorder(CompoundFunctionalIntegerExpression CompoundFunctionalIntegerExpression) {
        return true;
    }

    public boolean visitModuloPostorder(CompoundFunctionalIntegerExpression CompoundFunctionalIntegerExpression) {
        return true;
    }

    public boolean visitModuloPreorder(CompoundFunctionalIntegerExpression CompoundFunctionalIntegerExpression) {
        return true;
    }

    public boolean visitMultiplicationInorder(final CompoundFunctionalIntegerExpression multiplication) {
        return true;
    }

    public boolean visitMultiplicationPostorder(final CompoundFunctionalIntegerExpression multiplication) {
        return true;
    }

    public boolean visitMultiplicationPreorder(final CompoundFunctionalIntegerExpression multiplication) {
        return true;
    }

    public boolean visitNegationPostorder(final CompoundFunctionalIntegerExpression negation) {
        return true;
    }

    public boolean visitNegationPreorder(final CompoundFunctionalIntegerExpression negation) {
        return true;
    }

    public boolean visitPowerInorder(final CompoundFunctionalIntegerExpression power) {
        return true;
    }

    public boolean visitPowerPostorder(final CompoundFunctionalIntegerExpression power) {
        return true;
    }

    public boolean visitPowerPreorder(final CompoundFunctionalIntegerExpression power) {
        return true;
    }

    public boolean visitRemainderInorder(final CompoundFunctionalIntegerExpression remainder) {
        return true;
    }

    public boolean visitRemainderPostorder(final CompoundFunctionalIntegerExpression remainder) {
        return true;
    }

    public boolean visitRemainderPreorder(final CompoundFunctionalIntegerExpression remainder) {
        return true;
    }

    public boolean visitShiftLeftInorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitShiftLeftPostorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitShiftLeftPreorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitShiftRightInorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitShiftRightPostorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitSubtractionInorder(final CompoundFunctionalIntegerExpression subtraction) {
        return true;
    }

    public boolean visitSubtractionPostorder(final CompoundFunctionalIntegerExpression subtraction) {
        return true;
    }

    public boolean visitSubtractionPreorder(final CompoundFunctionalIntegerExpression subtraction) {
        return true;
    }

    public boolean visitUnsignedShiftRightInorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitUnsignedShiftRightPostorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitUnsignedShiftRightPreorder(final CompoundFunctionalIntegerExpression shift) {
        return true;
    }

    public boolean visitVarRef(final IntegerVariable varRef) {
        return true;
    }

    public boolean visitXorInorder(final CompoundFunctionalIntegerExpression xor) {
        return true;
    }

    public boolean visitXorPostorder(final CompoundFunctionalIntegerExpression xor) {
        return true;
    }

    public boolean visitXorPreorder(final CompoundFunctionalIntegerExpression xor) {
        return true;
    }

    protected boolean visit(final FunctionalIntegerExpression expression) {
        return expression.accept(this) != null;
    }

    private boolean callPostorderHook(CompoundFunctionalIntegerExpression exp) {
        switch (exp.getOperation()) {
            case ADD:
                return this.visitAdditionPostorder(exp);
            case AND:
                return this.visitConjunctionPostorder(exp);
            case TIDIV:
                return this.visitDivisionPostorder(exp);
            case EMOD:
                return this.visitModuloPostorder(exp);
            case MUL:
                return this.visitMultiplicationPostorder(exp);
            case NEG:
                return this.visitNegationPostorder(exp);
            case OR:
                return this.visitDisjunctionPostorder(exp);
            case POW:
                return this.visitPowerPostorder(exp);
            case TMOD:
                return this.visitRemainderPostorder(exp);
            case SHL:
                return this.visitShiftLeftPostorder(exp);
            case SHR:
                return this.visitShiftRightPostorder(exp);
            case SUB:
                return this.visitSubtractionPostorder(exp);
            case USHR:
                return this.visitUnsignedShiftRightPostorder(exp);
            case XOR:
                return this.visitXorPostorder(exp);
            default:
                throw new IllegalStateException("Someone found a new way to operate on integers");
        }

    }

    private boolean callPreorderHook(CompoundFunctionalIntegerExpression exp) {
        switch (exp.getOperation()) {
            case ADD:
                return this.visitAdditionPreorder(exp);
            case AND:
                return this.visitConjunctionPreorder(exp);
            case TIDIV:
                return this.visitDivisionPreorder(exp);
            case EMOD:
                return this.visitModuloPreorder(exp);
            case MUL:
                return this.visitMultiplicationPreorder(exp);
            case NEG:
                return this.visitNegationPreorder(exp);
            case OR:
                return this.visitDisjunctionPreorder(exp);
            case POW:
                return this.visitPowerPreorder(exp);
            case TMOD:
                return this.visitRemainderPreorder(exp);
            case SHL:
                return this.visitShiftLeftPreorder(exp);
            case SHR:
                return this.visitShiftRightPreorder(exp);
            case SUB:
                return this.visitSubtractionPreorder(exp);
            case USHR:
                return this.visitUnsignedShiftRightPreorder(exp);
            case XOR:
                return this.visitXorPreorder(exp);
            default:
                throw new IllegalStateException("Someone found a new way to operate on integers");
        }

    }

}
