/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * The solver will be used to transform the general OrderPolyConstraints
 * to some simple format that can actually be solved. The resulting form of
 * the constraints depends on the embedded solver being used. Any OPCSolver
 * starts the embedded solver after simplifying the constraints and returns the
 * solver's result.
 * @param <C> The type of the coefficients used in the polynomials.
 * @author cotto
 */
public interface OPCSolver<C extends GPolyCoeff> {
    /**
     * Take the given constraint (which might be a combination of several
     * constraints) and solve it using the built in solver. This might involve
     * some conversion to a more simple format, as most solvers will not work
     * on OrderPolyConstraints. After solving return a map which defines a value
     * for every variable which is quantified existentially in the constraint.
     * @param constraint The constraint that should be solved.
     * @param ranges The range for the variables.
     * @param defaultRange The range for all variables not mentioned in ranges.
     * @param aborter Stop searching as soon as the aborter gets active.
     * @return A map giving a value for every existentially quantified variable.
     * @throws AbortionException when the aborter kicks in.
     */
    Map<GPolyVar, C> solve(
            OrderPolyConstraint<C> constraint,
            Map<GPolyVar, OPCRange<C>> ranges,
            OPCRange<C> defaultRange,
            Abortion aborter) throws AbortionException;

    /**
     * @see solve(OrderPolyConstraint<C>, Map<GPolyVar, OPCRange<C>>,
     *      OPCRange<C>, Abortion) but acting on some domain
     * @param constraint
     *            The constraint that should be solved.
     * @param ranges
     *            The range for the variables.
     * @param defaultRange
     *            The range for all variables not mentioned in ranges.
     * @param aborter
     *            Stop searching as soon as the aborter gets active.
     * @return A map giving a value for every existentially quantified variable.
     * @throws AbortionException
     *             when the aborter kicks in.
     */
    Map<GPolyVar, C> solve(OrderPolyConstraint<C> constraint, Domain domain,
            Abortion aborter) throws AbortionException;

    /**
     * @param polyRingParam
     *            the polynomial ring.
     */
    void setPolyRing(Ring<GPoly<C, GPolyVar>> polyRingParam);

    /**
     * @param inner the flattening visitor for coefficient polys.
     */
    void setFvInner(FlatteningVisitor<C, GPolyVar> inner);

    /**
     * @param outer the flattening visitor for order polys.
     */
    void setFvOuter(FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer);

    /**
     * @return a copy of the OPC solver at hand which may be altered in every
     * possible way
     */
    OPCSolver<C> getCopy();
}
