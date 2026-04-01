/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * This represents a universal quantifier ("A").
 * @author cotto
 * @param <C> The type of the coefficients inside the constraint.
 */
public class OPCQuantifierA<C extends GPolyCoeff> extends OPCQuantifier<C> {

    /**
     * @param constraintParam The constraint over that the quantifier stretches.
     * @param variablesParam The variables covered by the quantifier.
     */
    public OPCQuantifierA(
            final OrderPolyConstraint<C> constraintParam,
            final Set<GPolyVar> variablesParam) {
        super(constraintParam, variablesParam);
    }

    /**
     * @return string representation.
     */
    @Override
    public String toString() {
        return "A(" + this.getVariables() + ")" + this.getInnerConstraint();
    }

    /**
     * Feed this constraint and its subconstraints to the visitor.
     * @param v The visitor that visits the whole constraint.
     * @return The constraint resulting from the visitor's changes.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseQuantifierA(this);
        OrderPolyConstraint<C> newConstraint =
            v.applyTo(this.getInnerConstraint());
        return v.caseQuantifierA(this, newConstraint);
    }
}
