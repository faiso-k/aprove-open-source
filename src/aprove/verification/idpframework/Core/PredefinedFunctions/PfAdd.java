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

public class PfAdd<I extends IntRing<I>> extends BinaryIntFunction<I, I> {

    public PfAdd(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Add, domains, true);
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Incr;
    }

    @Override
    protected IntegerDomain<I> determineResultDomain() {
        return (IntegerDomain<I>) this.domains.get(0);
    }

    @Override
    protected ITerm<I> intEvaluate(final I val1,
        final I val2, final IDPPredefinedMap predefinedMap) {
        return val1.add(val2).getTerm(predefinedMap);
    }

}
