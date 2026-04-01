/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public class PfEq<I extends IntRing<I>> extends BinaryIntRelation<I> {

    public PfEq(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Eq, domains);
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Wild;
    }

    @Override
    protected Boolean intBoolEvaluate(final I val1,
        final I val2) {
        return val1.semiCompareTo(val2) == 0;
    }

}
