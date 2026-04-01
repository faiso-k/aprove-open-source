/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * A comment wrapping an OrderPolyConstraint.
 *
 * Except for output, it should only be interpreted as its child.
 *
 * @param <C> The type of the coefficients used in the polynomials.
 */
public class OPCComment<C extends GPolyCoeff> implements OrderPolyConstraint<C> {

    private final String comment;
    private final OrderPolyConstraint<C> child;

    public OPCComment(String comment, OrderPolyConstraint<C> child) {
        this.comment = comment;
        this.child = child;
    }

    /**
     * "True" has no variables.
     * @return an empty set.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        return this.child.getFreeVariables();
    }

    /**
     * "True" is closed.
     * @return true
     */
    @Override
    public boolean isClosed() {
        return this.child.isClosed();
    }

    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseComment(this);
        OrderPolyConstraint<C> newSub = v.applyTo(this.child);
        return v.caseComment(this, this.comment, newSub);
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return "/*" + this.comment + "*/" + this.child;
    }

    @Override
    public int hashCode() {
        final int prime = 719;
        int result = 1;
        result = prime * result + ((this.child == null) ? 0 : this.child.hashCode());
        result = prime * result + ((this.comment == null) ? 0 : this.comment.hashCode());
        return result;
    }

    @Override
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
        OPCComment other = (OPCComment) obj;
        if (this.comment == null) {
            if (other.comment != null) {
                return false;
            }
        } else if (!this.comment.equals(other.comment)) {
            return false;
        }
        if (this.child == null) {
            if (other.child != null) {
                return false;
            }
        } else if (!this.child.equals(other.child)) {
            return false;
        }
        return true;
    }

    public String getComment() {
        return this.comment;
    }

}
