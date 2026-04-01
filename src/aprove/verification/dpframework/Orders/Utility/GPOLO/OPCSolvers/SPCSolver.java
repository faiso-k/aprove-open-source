/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * A SPCSolver takes SimplePolyConstraints and solves them somehow.
 * @author cotto
 */
public interface SPCSolver {
    /**
     * Find a solution for the given constraints.
     * @param constraints the constraints.
     * @param searchStrictConstraints the searchstrict constraints.
     * @param ranges the ranges for the variables.
     * @param defaultRange the range for all variables not mentioned in ranges.
     * @param aborter some aborter.
     * @return a value for every variable.
     * @throws AbortionException when the aborter kicks in.
     */
    Map<GPolyVar, BigInteger> search(
            Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints,
            Map<String, BigInteger> ranges,
            BigInteger defaultRange,
            Abortion aborter) throws AbortionException;
}
