/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * A negation of the subconstraint.
 * @author cotto
 * @param <C> The type of the coefficients used in the polynomials.
 */
public class OPCNot<C extends GPolyCoeff> implements OrderPolyConstraint<C> {
    /**
     * The subconstraint.
     */
    private final OrderPolyConstraint<C> sub;

    /**
     * Create a new NOT(sub) constraint.
     * @param subConstraint The subconstraint.
     */
    public OPCNot(final OrderPolyConstraint<C> subConstraint) {
        if (Globals.useAssertions) {
            assert(subConstraint != null);
        }
        this.sub = subConstraint;
    }
    /**
     * @return the free variables of the subconstraint.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        return this.sub.getFreeVariables();
    }

    /**
     * @return true iff the subconstraint is closed.
     */
    @Override
    public boolean isClosed() {
        return this.sub.isClosed();
    }

    /**
     * Just call the two methods of the visitor. Nothing else to see here..
     * @param v the visitor.
     * @return something defined by the visitor.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseNot(this);
        OrderPolyConstraint<C> newSub = v.applyTo(this.sub);
        return v.caseNot(this, newSub);
    }
    /**
     * @return the node behind this not.
     */
    public OrderPolyConstraint<C> getSub() {
        return this.sub;
    }

    /**
     * @return a string representation of this node.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("NOT(");
        sb.append(this.sub.toString());
        sb.append(")");
        return sb.toString();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.sub == null) ? 0 : this.sub.hashCode());
        return result;
    }
    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    @SuppressWarnings("unchecked")
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final OPCNot other = (OPCNot) obj;
        if (this.sub == null) {
            if (other.sub != null) {
                return false;
            }
        } else if (!this.sub.equals(other.sub)) {
            return false;
        }
        return true;
    }
}
