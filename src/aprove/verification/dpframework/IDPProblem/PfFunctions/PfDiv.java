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

public class PfDiv extends BinaryIntFunction {

    public PfDiv(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Div, domains, true);
    }

    @Override
    protected BigInteger intEvaluate(BigInteger val1, BigInteger val2) {
        return val1.divide(val2);
    }

    @Override
    public IDependence filterPositon(int i) {
        switch(i) {
        case 0: return IDependence.Incr;
        case 1: return IDependence.Decr;
        default : throw new IllegalArgumentException();
        }
    }

}
