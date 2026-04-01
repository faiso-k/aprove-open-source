/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public class PfGt<I extends IntRing<I>> extends BinaryIntRelation<I> {

    public PfGt(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Gt, domains);

    }

    @Override
    public IDependence filterPositon(final int i) {
        switch (i) {
        case 0:
            return IDependence.Incr;
        case 1:
            return IDependence.Decr;
        default:
            throw new IllegalArgumentException();
        }
    }

    @Override
    protected Boolean intBoolEvaluate(final I val1,
        final I val2) {
        return val1.semiCompareTo(val2) > 0;
    }

}
