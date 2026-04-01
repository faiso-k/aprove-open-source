/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Every junctor implementing this interface (AND, OR, ...) has a set of
 * operands.
 * @param <C> The type of the coefficients used in the polynomials.
 * @author cotto
 */
public abstract class OPCNaryJunctor<C extends GPolyCoeff>
    implements OrderPolyConstraint<C> {
    /**
     * The operands which are order poly constraints.
     */
    private Set<OrderPolyConstraint<C>> operands;

    /**
     * Cache the hashCode, because recursive computation is quite expensive.
     */
    private int hashCode = 0;

    /**
     * Set the operands.
     * @param param The operands.
     */
    protected void setOperands(final Set<OrderPolyConstraint<C>> param) {
        this.operands = param;
    }

    /**
     * @return the set of operands.
     */
    public Set<OrderPolyConstraint<C>> getOperands() {
        return this.operands;
    }

    /**
     * @return true iff all polys do not contain a free variable.
     */
    @Override
    public boolean isClosed() {
        for (OrderPolyConstraint<C> constraint : this.operands) {
            if (!constraint.isClosed()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return all free variables that occur in the polynomial.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        Set<GPolyVar> result = new LinkedHashSet<GPolyVar>();
        for (OrderPolyConstraint<C> constraint : this.operands) {
            result.addAll(constraint.getFreeVariables());
        }
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        if (this.hashCode == 0) {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.operands.hashCode();
            this.hashCode = result;
        }
        return this.hashCode;
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
        final OPCNaryJunctor other = (OPCNaryJunctor) obj;
        if (this.operands == null) {
            if (other.operands != null) {
                return false;
            }
        } else if (!this.operands.equals(other.operands)) {
            return false;
        }
        return true;
    }

}
