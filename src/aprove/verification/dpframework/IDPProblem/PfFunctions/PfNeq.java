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

public class PfNeq extends BinaryIntRelation {

    public PfNeq(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Neq, domains);
    }

    @Override
    protected Boolean intBoolEvaluate(BigInteger val1, BigInteger val2) {
        return val1.compareTo(val2) > 0;
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }

}
