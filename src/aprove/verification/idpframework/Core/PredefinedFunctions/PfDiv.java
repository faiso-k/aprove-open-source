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

public class PfDiv<I extends IntRing<I>> extends BinaryIntFunction<I, I> {

    public PfDiv(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Div, domains, true);
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
    protected ITerm<I> intEvaluate(final I val1,
        final I val2, final IDPPredefinedMap predefinedMap) {
        if (val2.isZero()) {
            return null;
        } else {
            return val1.div(val2).getTerm(predefinedMap);
        }
    }

    @Override
    protected IntegerDomain<I> determineResultDomain() {
        return (IntegerDomain<I>) this.domains.get(0);
    }

}
