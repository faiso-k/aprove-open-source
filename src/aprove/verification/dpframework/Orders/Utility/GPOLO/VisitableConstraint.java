/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * A visitable constraint provides a method "visit" that, when called, feeds
 * itself and all subconstraints to the given visitor.
 * @param <C> The type of the coefficients used in the polynomials.
 * @author cotto
 */
public interface VisitableConstraint<C extends GPolyCoeff> {
    /**
     * Feed this constraint and all subconstraints to the visitor.
     * @param v The visitor.
     * @return The resulting constraint as defined by the visitor.
     */
    OrderPolyConstraint<C> visit(ConstraintVisitor<C> v);
}
