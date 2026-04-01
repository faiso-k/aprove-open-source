/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * This represents an existential quantifier ("E").
 * @author cotto
 * @param <C> The type of the coefficients inside the constraint.
 */
public class OPCQuantifierE<C extends GPolyCoeff> extends OPCQuantifier<C> {

    /**
     * @param constraintParam The constraint over that the quantifier stretches.
     * @param variablesParam The variables covered by the quantifier.
     */
    public OPCQuantifierE(
            final OrderPolyConstraint<C> constraintParam,
            final Set<GPolyVar> variablesParam) {
        super(constraintParam, variablesParam);
    }

    /**
     * @return string representation.
     */
    @Override
    public String toString() {
        return "E(" + this.getVariables() + ")" + this.getInnerConstraint();
    }

    /**
     * Feed this constraint and its subconstraints to the visitor.
     * @param v The visitor that visits the whole constraint.
     * @return The constraint resulting from the visitor's changes.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseQuantifierE(this);
        OrderPolyConstraint<C> newConstraint =
            v.applyTo(this.getInnerConstraint());
        return v.caseQuantifierE(this, newConstraint);
    }
}
