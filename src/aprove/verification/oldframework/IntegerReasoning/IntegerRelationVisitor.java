package aprove.verification.oldframework.IntegerReasoning;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * @author Alexander Weinert
 */
public abstract class IntegerRelationVisitor implements Visitor<Expression, Expression> {

    @Override
    public Expression visit(Expression v) {
        if (v instanceof IntegerRelation) {
            IntegerRelation rel = (IntegerRelation)v;
            final boolean continueTraversal = this.visitRelation(rel.getLhs(), rel.getRhs());
            if (!continueTraversal) {
                return rel;
            }
            switch (rel.getRelationType()) {
                case EQ:
                    this.visitEqualsRelation(rel.getLhs(), rel.getRhs());
                    break;
                case LE:
                    this.visitLessThanEqualsRelation(rel.getLhs(), rel.getRhs());
                    break;
                case LT:
                    this.visitLessThanRelation(rel.getLhs(), rel.getRhs());
                    break;
                case GE:
                    this.visitLessThanEqualsRelation(rel.getRhs(), rel.getLhs());
                    break;
                case GT:
                    this.visitLessThanRelation(rel.getRhs(), rel.getLhs());
                    break;
                case NE:
                    this.visitNotEqualsRelation(rel.getLhs(), rel.getRhs());
                    break;
                default:
                    assert false : "Someone found a new way to relate integers";
                break;
            }
        }
        return v;
    }

    /**
     * Asks the relation to first call this.visitRelation with its lhs and rhs
     * and to call the more specific method corresponding to the type of the
     * relation afterwards
     * @param relation Some relation
     */
    public void visit(final IntegerRelation relation) {
        relation.accept(this);
    }

    /**
     * Is called when a relation of the form expr_1 = expr_2 is visited
     * @param lhs The left hand side of the relation
     * @param rhs The right hand side of the relation
     */
    public void visitEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        // Empty standard implementation
    }

    /**
     * Is called when a relation of the form expr_1 <= expr_2 is visited
     * @param lhs The left hand side of the relation
     * @param rhs The right hand side of the relation
     */
    public void visitLessThanEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        // Empty standard implementation
    }

    /**
     * Is called when a relation of the form expr_1 < expr_2 is visited
     * @param lhs The left hand side of the relation
     * @param rhs The right hand side of the relation
     */
    public void visitLessThanRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        // Empty standard implementation
    }

    /**
     * Is called when a relation of the form expr_1 != expr_2 is visited
     * @param lhs The left hand side of the relation
     * @param rhs The right hand side of the relation
     */
    public void visitNotEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        // Empty standard implementation
    }

    /**
     * Is called for every relation before one of the more specific methods.
     * If this method returns false, the more specific method is not called
     * at all.
     * @param lhs The left hand side of the relation
     * @param rhs The right hand side of the relation
     * @return True if the more specific method should be called
     */
    public boolean visitRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        return true;
    }

}
