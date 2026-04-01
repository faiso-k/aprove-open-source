/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * A conjunction of two constraints.
 * @param <C> The type of the coefficients used in the polynomials.
 * @author cotto
 */
public class OPCAnd<C extends GPolyCoeff> extends OPCNaryJunctor<C> {
    /**
     * Create a constraint which represents "one AND two AND ...".
     * @param constraints Some constraints one, two, ...
     */
    @SuppressWarnings("unchecked")
    OPCAnd(final Set<OrderPolyConstraint<C>> constraints) {
        if (Globals.useAssertions) {
            assert (constraints.size() > 1 && !constraints.contains(null));
        }
        Set<OrderPolyConstraint<C>> newSet =
            new LinkedHashSet<OrderPolyConstraint<C>>(constraints.size());
        for (OrderPolyConstraint<C> elem : constraints) {
            if (elem instanceof OPCAnd) {
                OPCAnd<C> and = (OPCAnd<C>) elem;
                newSet.addAll(and.getOperands());
            } else {
                newSet.add(elem);
            }
        }
        this.setOperands(newSet);
    }

    /**
     * Create a constraint which represents "one AND two".
     * @param one The first subconstraint.
     * @param two The second subconstraint.
     */
    @SuppressWarnings("unchecked")
    OPCAnd(final OrderPolyConstraint<C> one, final OrderPolyConstraint<C> two) {
        if (Globals.useAssertions) {
            assert (one != null && two != null);
        }
        Set<OrderPolyConstraint<C>> set =
            new LinkedHashSet<OrderPolyConstraint<C>>(2);
        if (one instanceof OPCAnd) {
            OPCAnd<C> and = (OPCAnd<C>) one;
            set.addAll(and.getOperands());
        } else {
            set.add(one);
        }
        if (two instanceof OPCAnd) {
            OPCAnd<C> and = (OPCAnd<C>) two;
            set.addAll(and.getOperands());
        } else {
            set.add(two);
        }
        this.setOperands(set);
    }

    /**
     * Feed this constraint and its subconstraints to the visitor.
     * @param v The visitor that visits the whole constraint.
     * @return The constraint resulting from the visitor's changes.
     */
    @Override
    public OrderPolyConstraint<C> visit(final ConstraintVisitor<C> v) {
        v.fcaseAnd(this);
        Set<OrderPolyConstraint<C>> set =
            new LinkedHashSet<OrderPolyConstraint<C>>(
                    this.getOperands().size());
        for (OrderPolyConstraint<C> constraint : this.getOperands()) {
            set.add(v.applyTo(constraint));
        }
        return v.caseAnd(this, set);
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("AND(");
        boolean notFirst = false;
        for (OrderPolyConstraint<C> constraint : this.getOperands()) {
            if (notFirst) {
                sb.append(",");
            }
            else {
                notFirst = true;
            }
            sb.append(constraint.toString());
        }
        sb.append(")");
        return sb.toString();
    }
}
