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

public class PfMod extends BinaryIntFunction {

    public PfMod(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Mod, domains, true);
    }

    @Override
    protected BigInteger intEvaluate(BigInteger val1, BigInteger val2) {
        // FIXME: semantics?
        return val1.remainder(val2);
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }



}
