/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public interface IdpShapeHeuristic {

    /**
     * @param interpretation
     * @param f
     * @return null for using default shape (like linear...) OR
     *         x: shape (X1, X2, ...)
     *         y: side constraints
     *         z: map position (0, 1, ...) -> constraint for increasin / decreasing
     */
    public Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> getShape(IDPGInterpretation interpretation, FunctionSymbol f,
            Abortion aborter) throws AbortionException;

    /**
     * @param interpretation
     * @return true iff heuristics supplies a shape for the idp problem
     */
    public boolean applies(IDPGInterpretation interpretation);

}
