/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Just true.
 * @author cotto
 * @param <C> The type of the coefficients used in the polynomials.
 */
public class OPCTrue<C extends GPolyCoeff> implements OrderPolyConstraint<C> {
    /**
     * The standard true object.
     */
    @SuppressWarnings("unchecked")
    private static final OPCTrue TRUE = new OPCTrue();

    /**
     * @return the type correct standard true object.
     * @param <C> The type of the coefficients used in the polynomials.
     */
    @SuppressWarnings("unchecked")
    public static <C extends GPolyCoeff> OPCTrue<C> getTrue() {
        return (OPCTrue<C>) OPCTrue.TRUE;
    }

    /**
     * "True" has no variables.
     * @return an empty set.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        return Collections.<GPolyVar>emptySet();
    }

    /**
     * "True" is closed.
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
        v.fcaseTrue(this);
        return v.caseTrue(this);
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return "True";
    }

    /**
     * @return true iff obj also is a OPCTrue object.
     * @param obj some object.
     */
    @Override
    public boolean equals(final Object obj) {
        return (obj != null && obj instanceof OPCTrue);
    }

    /**
     * @return some hash code.
     */
    @Override
    public int hashCode() {
        final int hashCode = 452348925;
        return hashCode;
    }
}
