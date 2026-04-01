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

public class PfLe extends BinaryIntRelation {

    public PfLe(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Le, domains);
    }

    @Override
    protected Boolean intBoolEvaluate(BigInteger val1, BigInteger val2) {
        return val1.compareTo(val2) <= 0;
    }

    @Override
    public IDependence filterPositon(int i) {
        switch(i) {
        case 0: return IDependence.Decr;
        case 1: return IDependence.Incr;
        default : throw new IllegalArgumentException();
        }
    }

}
