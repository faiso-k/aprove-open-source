/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface LogOPCSolver<C extends GPolyCoeff> extends OPCSolver<C> {

    /**
     * Similar to solve(), but additionally returns the values for OPCLogVars.
     * @throws AbortionException
     */
    Pair<Map<GPolyVar, BigIntImmutable>, Map<OPCLogVar<BigIntImmutable>, Boolean>>  solveLog (
            OrderPolyConstraint<C> constraint,
            Map<GPolyVar, OPCRange<C>> ranges,
            OPCRange<C> defaultRange,
            Abortion aborter) throws AbortionException;

    public static interface LogOPCSolverFactory<C extends GPolyCoeff> {

        public LogOPCSolver<C> newSolver();

    }

}
