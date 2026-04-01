package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;

/**
 * A binary relation over integer expressions.
 * @author cryingshadow
 * @version $Id$
 */
public interface IntegerRelation
extends BinaryExpression, IntegerExpression, RelationExpression, SMTSExpressible<SBool> {

    @Override
    default IntegerRelation applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    default IntegerRelation applySubstitution(Substitution sigma) {
        return Substitution.applySubstitution(this, sigma);
    }

    @Override
    default IntegerRelation applySubstitution(Variable v, Expression e) {
        return Expression.applySubstitution(this, v, e);
    }

    @Override
    FunctionalIntegerExpression getLhs();

    @Override
    default String getName() {
        return this.getRelationType().toString();
    }

    /**
     * @return The type of this relation.
     */
    IntegerRelationType getRelationType();

    @Override
    FunctionalIntegerExpression getRhs();

    @Override
    @SuppressWarnings("unchecked")
    default Set<? extends IntegerVariable> getVariables() {
        return (Set<? extends IntegerVariable>)CompoundExpression.getVariables(this);
    }

    /**
     * @return True iff this relation is a directed inequality.
     */
    default boolean isDirectedInequality() {
        switch (this.getRelationType()) {
            case LE:
            case LT:
            case GE:
            case GT:
                return true;
            default:
                return false;
        }
    }

    /**
     * @return True iff this relation is an equation.
     */
    default boolean isEquation() {
        return this.getRelationType() == IntegerRelationType.EQ;
    }

    /**
     * @return True iff this relation is a strict directed inequality.
     */
    default boolean isStrictDirectedInequality() {
        return this.isDirectedInequality() && this.isStrictInequality();
    }

    /**
     * @return True iff this relation is a strict inequality.
     */
    default boolean isStrictInequality() {
        switch (this.getRelationType()) {
            case NE:
            case LT:
            case GT:
                return true;
            default:
                return false;
        }
    }

    /**
     * @return True iff this relation is an undirected inequality.
     */
    default boolean isUndirectedInequality() {
        return this.getRelationType() == IntegerRelationType.NE;
    }

    /**
     * @return True iff this relation is a weak directed inequality.
     */
    default boolean isWeakDirectedInequality() {
        return this.isDirectedInequality() && !this.isStrictInequality();
    }

    /**
     * @return A relation that holds iff this relation does not hold.
     */
    IntegerRelation negate();

    @Override
    default IntegerRelation setLhs(Expression lhs) {
        return this.setLhs((FunctionalIntegerExpression)lhs);
    }

    /**
     * @param lhs The new left-hand side.
     * @return An integer relation with the specified left-hand side and the current right-hand side.
     */
    IntegerRelation setLhs(FunctionalIntegerExpression lhs);

    @Override
    default IntegerRelation setRhs(Expression rhs) {
        return this.setRhs((FunctionalIntegerExpression)rhs);
    }

    /**
     * @param rhs The new right-hand side.
     * @return An integer relation with the current left-hand side and the specified right-hand side.
     */
    IntegerRelation setRhs(FunctionalIntegerExpression rhs);

    @Override
    default SMTExpression<SBool> toSMTExp() {
        SMTExpression<SInt> leftValue = this.getLhs().toSMTExp();
        SMTExpression<SInt> rightValue = this.getRhs().toSMTExp();
        if (leftValue == null || rightValue == null) {
            return Core.True;
        }
        switch (this.getRelationType()) {
            case GT:
                return Ints.greater(leftValue, rightValue);
            case GE:
                return Ints.greaterEqual(leftValue, rightValue);
            case LT:
                return Ints.less(leftValue, rightValue);
            case LE:
                return Ints.lessEqual(leftValue, rightValue);
            case EQ:
                return Core.equivalent(leftValue, rightValue);
            case NE:
                return Core.not(Core.equivalent(leftValue, rightValue));
            default:
                throw new IllegalStateException("Unknown relation type");
        }
    }

}
