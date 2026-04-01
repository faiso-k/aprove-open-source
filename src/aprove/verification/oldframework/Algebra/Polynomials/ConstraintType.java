package aprove.verification.oldframework.Algebra.Polynomials;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Orders.Utility.*;


/**
 * Encodes the type of constraint we are dealing with:
 * Is the (Simple/Var/...)Polynomial on the LHS
 * equal to/greater or equal/greater than 0?
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public enum ConstraintType implements Exportable {
    EQ("="),
    GE(">="),
    GT(">");

    private final String rep;

    private ConstraintType(String rep) {
        this.rep = rep;
    }

    /**
     * Returns the ConstraintType that corresponds to a Relation.
     * @param rel Some relation.
     * @param strict If false, a strict greater-than relation is
     * converted into a weak, greater-or-equal constraint type.
     */
    public static ConstraintType fromRelation(OrderRelation rel, boolean strict) {
        switch(rel) {
        case EQ : return ConstraintType.EQ;
        case GE : return ConstraintType.GE;
        case GR : return strict ? ConstraintType.GT : ConstraintType.GE;
        default : throw new IllegalArgumentException("Unknown relation type " + rel);
        }
    }

    @Override
    public String toString() {
        return this.rep;
    }

    @Override
    public String export(Export_Util o) {
        switch(this) {
        case EQ : return o.eqSign();
        case GE : return o.geSign();
        case GT : return o.gtSign();
        default : throw new UnsupportedOperationException("Unknown relation type" + this);
        }
    }
}

