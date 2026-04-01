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

public class IdpDefaultShapeHeuristic implements IdpShapeHeuristic {

    @Override
    public Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> getShape(
            IDPGInterpretation interpretation, FunctionSymbol f, Abortion aborter) {
        return null;
    }

    @Override
    public boolean applies(IDPGInterpretation interpretation) {
        return false;
    }

}
