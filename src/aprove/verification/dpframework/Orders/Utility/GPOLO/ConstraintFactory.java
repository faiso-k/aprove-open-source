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
 * Factories implementing this interface will be used to create
 * OrderPolyConstraints.
 * @author cotto
 * @param <C> The type of the coefficients inside the constraints.
 */
public interface ConstraintFactory<C extends GPolyCoeff> {
    /**
     * @return an OrderPolyConstraint that always is true.
     */
    OrderPolyConstraint<C> createTrue();

    /**
     * @return an OrderPolyConstraint that always is false.
     */
    OrderPolyConstraint<C> createFalse();

    /**
     * @param name the variable name
     * @return an OrderPolyConstraint that represents a logical variable.
     */
    OPCLogVar<C> createLogVar(String name);

    /**
     * Build a constraint A(x,y,z) (poly REL 0) where A(x,y,z) is the universal
     * quantifier. Here x,y,z are the variables of the outer polynomial.
     * @param leftPoly The polynomial used to create the left-hand side of the constraint.
     * @param rightPoly The polynomial used to create the right-hand side of the constraint.
     * @param ct The constraint type (relation).
     * @return A constraint A(x,y,z) (poly REL 0).
     */
    OrderPolyConstraint<C> createWithQuantifier(
            OrderPoly<C> poly, ConstraintType ct);

    /**
     * Build a constraint A(x,y,z) (leftPoly REL rightPoly) where A(x,y,z) is the universal
     * quantifier. Here x,y,z are the variables of the outer polynomial.
     * @param leftPoly The polynomial used to create the left-hand side of the constraint.
     * @param rightPoly The polynomial used to create the right-hand side of the constraint.
     * @param ct The constraint type (relation).
     * @return A constraint A(x,y,z) (leftPoly REL rightPoly).
     */
    OrderPolyConstraint<C> createWithQuantifier(
            OrderPoly<C> leftPoly, OrderPoly<C> rightPoly, ConstraintType ct);

    /**
     * Build a single constraint which is the disjunction of the given
     * constraints.
     * @param constraints A set of constraints.
     * @return A single constraint which is a disjunction of all given
     * constraints.
     */
    OrderPolyConstraint<C> createOr(
            Set<OrderPolyConstraint<C>> constraints);

    /**
     * Builds a constraint with a comment
     */
    OrderPolyConstraint<C> createComment(
            String comment, OrderPolyConstraint<C> child);

    /**
     * Build a single constraint which is the disjunction of the given
     * constraints.
     * @param first one constraint.
     * @param second another constraint.
     * @return A single constraint which is a disjunction of the given
     * constraints.
     */
    OrderPolyConstraint<C> createOr(
            OrderPolyConstraint<C> first,
            OrderPolyConstraint<C> second);

    /**
     * Build a single constraint which is the conjunction of the given
     * constraints.
     * @param constraints A set of constraints.
     * @return A single constraint which is a conjunction of all given
     * constraints.
     */
    OrderPolyConstraint<C> createAnd(
            Set<OrderPolyConstraint<C>> constraints);

    /**
     * Build a single constraint which is the conjunction of the given
     * constraints.
     * @param first one constraint.
     * @param second another constraint.
     * @return A single constraint which is a conjunction of the given
     * constraints.
     */
    OrderPolyConstraint<C> createAnd(
            OrderPolyConstraint<C> first,
            OrderPolyConstraint<C> second);

    /**
     * @param sub The constraint.
     * @param vars The variables subject to the quantifier.
     * @return a constraint which existentially quantifies over the given
     * variables.
     */
    OrderPolyConstraint<C> createQuantifierE(
            OrderPolyConstraint<C> sub,
            Set<GPolyVar> vars);

    /**
     * @param sub the constraint.
     * @return a constraint which negates sub.
     */
    OrderPolyConstraint<C> createNot(
            OrderPolyConstraint<C> sub);

}
