/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Just false.
 * @author cotto
 * @param <C> The type of the coefficients used in the polynomials.
 */
public class OPCFalse<C extends GPolyCoeff> implements OrderPolyConstraint<C> {
    /**
     * The standard false object.
     */
    @SuppressWarnings("unchecked")
    private static final OPCFalse FALSE = new OPCFalse();

    /**
     * @return the type correct standard false object.
     * @param <C> The type of the coefficients used in the polynomials.
     */
    @SuppressWarnings("unchecked")
    public static <C extends GPolyCoeff> OPCFalse<C> getFalse() {
        return (OPCFalse<C>) OPCFalse.FALSE;
    }

    /**
     * "False" has no variables.
     * @return an empty set.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        return Collections.<GPolyVar>emptySet();
    }

    /**
     * "False" is closed.
     * @return true
     */
    @Override
    public boolean isClosed() {
        return true;
    }

    /**
     * Just call the two methods of the visitor. Nothing else to see here..
     * @param v the visitor.
     * @return something defined by the visitor.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseFalse(this);
        return v.caseFalse(this);
    }

    /**
     * @return true iff obj also is a OPCFalse object.
     * @param obj some object.
     */
    @Override
    public boolean equals(final Object obj) {
        return (obj != null && obj instanceof OPCFalse);
    }

    /**
     * @return some hash code.
     */
    @Override
    public int hashCode() {
        final int hashCode = 452358925;
        return hashCode;
    }

    @Override
    public String toString() {
        return "False";
    }
}
