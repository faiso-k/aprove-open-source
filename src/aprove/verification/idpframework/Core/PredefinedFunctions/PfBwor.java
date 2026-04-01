/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public class PfBwor<I extends IntRing<I>> extends BinaryBitwiseIntFunction<I> {

    public PfBwor(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Bwor, domains);
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Wild;
    }

    @Override
    protected ITerm<I> intEvaluate(final I val1,
        final I val2, final IDPPredefinedMap predefinedMap) {
        return val1.bitwiseOr(val2).getTerm(predefinedMap);
    }

}
