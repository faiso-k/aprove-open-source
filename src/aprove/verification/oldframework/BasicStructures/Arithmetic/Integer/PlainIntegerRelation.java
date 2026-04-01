package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import aprove.*;

/**
 * The most simple structure implementing an integer relation.
 * @author cryingshadow
 * @version $Id$
 */
public class PlainIntegerRelation implements IntegerRelation {

    /**
     * The left-hand side.
     */
    private final FunctionalIntegerExpression lhs;

    /**
     * The right-hand side.
     */
    private final FunctionalIntegerExpression rhs;

    /**
     * The type of the relation (corresponds to relational operator).
     */
    private final IntegerRelationType type;

    /**
     * @param relType The type of the relation.
     * @param left The left-hand side of the relation.
     * @param right The right-hand side of the relation.
     */
    public PlainIntegerRelation(
        IntegerRelationType relType,
        FunctionalIntegerExpression left,
        FunctionalIntegerExpression right
    ) {
        if (Globals.useAssertions) {
            assert (relType != null) : "Relation without type detected!";
            assert (left != null) : "Relation without left-hand side detected!";
            assert (right != null) : "Relation without right-hand side detected!";
        }
        this.type = relType;
        this.lhs = left;
        this.rhs = right;
    }

    @Override
    public FunctionalIntegerExpression getLhs() {
        return this.lhs;
    }

    @Override
    public IntegerRelationType getRelationType() {
        return this.type;
    }

    @Override
    public FunctionalIntegerExpression getRhs() {
        return this.rhs;
    }

    @Override
    public PlainIntegerRelation negate() {
        return new PlainIntegerRelation(this.getRelationType().invert(), this.getLhs(), this.getRhs());
    }

    @Override
    public IntegerRelation setLhs(FunctionalIntegerExpression newLhs) {
        return new PlainIntegerRelation(this.getRelationType(), newLhs, this.getRhs());
    }

    @Override
    public IntegerRelation setRhs(FunctionalIntegerExpression newRhs) {
        return new PlainIntegerRelation(this.getRelationType(), newRhs, this.getRhs());
    }

}
