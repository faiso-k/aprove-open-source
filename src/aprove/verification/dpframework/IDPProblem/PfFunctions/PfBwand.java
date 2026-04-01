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

public class PfBwand extends BinaryBitwiseIntFunction {

    public PfBwand(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Bwand, domains);
    }

    @Override
    protected BigInteger intEvaluate(BigInteger val1, BigInteger val2) {
        return val1.and(val2);
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }

}
