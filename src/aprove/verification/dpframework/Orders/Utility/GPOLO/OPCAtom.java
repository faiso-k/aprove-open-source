/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * An atomic constraint of the form leftPoly REL rightPoly.
 * Caution: several old solvers expect the right side to be empty!
 *
 * @author cotto
 * @param <C> The type of the coefficients (deep) inside the polynomial.
 */
public class OPCAtom<C extends GPolyCoeff>
    implements OrderPolyConstraint<C> {
    /**
     * The polynomials.
     */
    private final OrderPoly<C> leftPoly, rightPoly;

    /**
     * The type of the constraint (relation of leftPoly to rightPoly).
     */
    private final ConstraintType ct;

    /**
     * Create an atom defined by the polynomials and the relation.
     * @param leftPolyParam The polynomial on the lhs.
     * @param rightPolyParam The polynomial on the rhs.
     * @param ctParam The type of the constraint (relation).
     */
    public OPCAtom(final OrderPoly<C> leftPolyParam,
            final OrderPoly<C> rightPolyParam,
            final ConstraintType ctParam) {
        this.leftPoly = leftPolyParam;
        this.rightPoly = rightPolyParam;
        this.ct = ctParam;
    }

    /**
     * @return true iff the polys do not contain a variable.
     */
    @Override
    public boolean isClosed() {
        if (this.rightPoly == null) {
            return !this.leftPoly.containsVariable();
        } // else
        return !this.leftPoly.containsVariable()
            && !this.rightPoly.containsVariable();
    }

    /**
     * @return the constraint's left hand side.
     */
    public OrderPoly<C> getLeftPoly() {
        return this.leftPoly;
    }

    /**
     * @return the constraint's right hand side.
     */
    public OrderPoly<C> getRightPoly() {
        return this.rightPoly;
    }

    /**
     * @return all variables that occur in the polynomials.
     */
    @Override
    public Set<GPolyVar> getFreeVariables() {
        Set<GPolyVar> result = new LinkedHashSet<GPolyVar>();
        if (this.leftPoly != null) {
            result.addAll(this.leftPoly.getVariables());
            result.addAll(this.leftPoly.getInnerVariables());
        }
        if (this.rightPoly != null) {
            result.addAll(this.rightPoly.getVariables());
            result.addAll(this.rightPoly.getInnerVariables());
        }
        return result;
    }

    /**
     * @return string representation.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(this.leftPoly.toString());
        sb.append(" ");
        sb.append(this.ct.toString());
        if (this.rightPoly == null) {
            sb.append(" 0");
        } else {
            sb.append(" ");
            sb.append(this.rightPoly.toString());
        }
        return sb.toString();
    }

    /**
     * @return the constraint type.
     */
    public ConstraintType getConstraintType() {
        return this.ct;
    }

    /**
     * Feed this constraint to the visitor.
     * @param v The visitor that visits the whole constraint.
     * @return The constraint resulting from the visitor's changes.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseAtom(this);
        return v.caseAtom(this);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.ct == null) ? 0 : this.ct.hashCode());
        result = prime * result
                + ((this.leftPoly == null) ? 0 : this.leftPoly.hashCode());
        result = prime * result
                + ((this.rightPoly == null) ? 0 : this.rightPoly.hashCode());
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
        if (obj == null || !(obj instanceof OPCAtom)) {
            return false;
        }
        final OPCAtom<C> other = (OPCAtom<C>) obj;
        if (this.ct == null) {
            if (other.ct != null) {
                return false;
            }
        } else if (!this.ct.equals(other.ct)) {
            return false;
        }
        if (this.leftPoly == null) {
            if (other.leftPoly != null) {
                return false;
            }
        } else if (!this.leftPoly.equals(other.leftPoly)) {
            return false;
        }
        if (this.rightPoly == null) {
            if (other.rightPoly != null) {
                return false;
            }
        } else if (!this.rightPoly.equals(other.rightPoly)) {
            return false;
        }
        return true;
    }
}
