/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public class PfBwnot<I extends IntRing<I>> extends IntFunction<I, I> {

    public PfBwnot(final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(PredefinedFunction.Func.Bwnot, domains, false);
    }

    @Override
    protected IntegerDomain<I> determineResultDomain() {
        return (IntegerDomain<I>) this.domains.get(0);
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Wild;
    }

    @Override
    public boolean isBitwise() {
        return true;
    }

    @Override
    public ITerm<I> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        final I bi =
            PredefinedUtil.getIntValue(t.get(0), this.domains.get(0));

        if (bi == null) {
            return null;
        } else {
            return bi.bitwiseNot().getTerm(predefinedMap);
        }
    }

}
