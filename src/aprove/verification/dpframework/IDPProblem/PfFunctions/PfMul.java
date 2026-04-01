/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.math.*;

import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import immutables.*;

public class PfMul extends BinaryIntFunction {

    public PfMul(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Mul, domains, true);
    }

    @Override
    protected BigInteger intEvaluate(BigInteger val1, BigInteger val2) {
        return val1.multiply(val2);
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }

}
