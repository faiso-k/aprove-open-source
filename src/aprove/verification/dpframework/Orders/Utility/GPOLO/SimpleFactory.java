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
 * @author cotto
 * @param <C> The type of the coefficients used inside the polynomials.
 */
public class SimpleFactory<C extends GPolyCoeff>
    implements ConstraintFactory<C> {

    /**
     * Build a single constraint which is the disjunction of the given
     * constraints.
     * @param constraints A set of constraints.
     * @return A single constraint which is a disjunction of all given
     * constraints.
     */
    @Override
    public OrderPolyConstraint<C> createOr(
            final Set<OrderPolyConstraint<C>> constraints) {
        if (constraints.size() == 0) {
            return new OPCFalse<C>();
        } else if (constraints.size() == 1) {
            return constraints.iterator().next();
        } else {
            return new OPCOr<C>(constraints);
        }
    }

    /**
     * Build a single constraint which is the conjunction of the given
     * constraints.
     * @param constraints A set of constraints.
     * @return A single constraint which is a conjunction of all given
     * constraints.
     */
    @Override
    public OrderPolyConstraint<C> createAnd(
            final Set<OrderPolyConstraint<C>> constraints) {
        int size = constraints.size();
        if (size == 0) {
            return new OPCTrue<C>();
        } else if (size == 1) {
            return constraints.iterator().next();
        } else {
            return new OPCAnd<C>(constraints);
        }
    }

    /**
     * Build a constraint (A(x,y,z) poly) REL 0 where A(x,y,z) is the universal
     * quantifier. Here x,y,z are the variables of the outer polynomial.
     * @param poly The polynomial used to create the constraint.
     * @param ct The constraint type (relation wrt. 0).
     * @return A constraint (A(x,y,z) poly) REL 0.
     */
    @Override
    public OrderPolyConstraint<C> createWithQuantifier(
            final OrderPoly<C> poly,
            final ConstraintType ct) {
        Set<GPolyVar> outerVars = poly.getVariables();
        OrderPolyConstraint<C> atom = new OPCAtom<C>(poly, null, ct);
        OrderPolyConstraint<C> temp = new OPCQuantifierA<C>(atom, outerVars);
        return temp;
    }

    /**
     * Build a constraint A(x,y,z) (leftPoly REL rightPoly) where A(x,y,z) is the universal
     * quantifier. Here x,y,z are the variables of the outer polynomial.
     * @param leftPoly The polynomial used to create the left-hand side of the constraint.
     * @param rightPoly The polynomial used to create the right-hand side of the constraint.
     * @param ct The constraint type (relation).
     * @return A constraint A(x,y,z) (leftPoly REL rightPoly).
     */
    @Override
    public OrderPolyConstraint<C> createWithQuantifier(
            final OrderPoly<C> leftPoly,
            final OrderPoly<C> rightPoly,
            final ConstraintType ct) {
        if (rightPoly == null) {
            return this.createWithQuantifier(leftPoly, ct);
        }
        Set<GPolyVar> outerVars = new LinkedHashSet<GPolyVar>();
        if (leftPoly != null) {
            outerVars.addAll(leftPoly.getVariables());
        }
        outerVars.addAll(rightPoly.getVariables());
        OrderPolyConstraint<C> atom = new OPCAtom<C>(leftPoly, rightPoly, ct);
        OrderPolyConstraint<C> temp = new OPCQuantifierA<C>(atom, outerVars);
        return temp;
    }

    /**
     * Build a single constraint which is the conjunction of the given
     * constraints.
     * @param first one constraint.
     * @param second another constraint.
     * @return A single constraint which is a conjunction of the given
     * constraints.
     */
    @Override
    public OrderPolyConstraint<C> createAnd(
            final OrderPolyConstraint<C> first,
            final OrderPolyConstraint<C> second) {
        return new OPCAnd<C>(first, second);
    }

    /**
     * Build a single constraint which is the disjunction of the given
     * constraints.
     * @param first one constraint.
     * @param second another constraint.
     * @return A single constraint which is a disjunction of the given
     * constraints.
     */
    @Override
    public OrderPolyConstraint<C> createOr(
            final OrderPolyConstraint<C> first,
            final OrderPolyConstraint<C> second) {
        return new OPCOr<C>(first, second);
    }

    /**
     * @return an OrderPolyConstraint that always is false.
     */
    @Override
    public OrderPolyConstraint<C> createFalse() {
        return OPCFalse.<C>getFalse();
    }

    /**
     * @return an OrderPolyConstraint that always is true.
     */
    @Override
    public OrderPolyConstraint<C> createTrue() {
        return OPCTrue.<C>getTrue();
    }

    @Override
    public OPCLogVar<C> createLogVar(String name) {
        return new OPCLogVar<C>(name);
    }

    /**
     * @param sub the constraint.
     * @param vars The variables to be quantified.
     * @return a constraint (E(a,b,c) sub).
     */
    @Override
    public OrderPolyConstraint<C> createQuantifierE(
            final OrderPolyConstraint<C> sub,
            final Set<GPolyVar> vars) {
        OrderPolyConstraint<C> temp = new OPCQuantifierE<C>(sub, vars);
        return temp;
    }

    /**
     * @param sub the constraint.
     * @return a not node.
     */
    @Override
    public OrderPolyConstraint<C> createNot(final OrderPolyConstraint<C> sub) {
        return new OPCNot<C>(sub);
    }

    @Override
    public OrderPolyConstraint<C> createComment(String comment,
            OrderPolyConstraint<C> child) {
        return new OPCComment<C>(comment, child);
    }

}
