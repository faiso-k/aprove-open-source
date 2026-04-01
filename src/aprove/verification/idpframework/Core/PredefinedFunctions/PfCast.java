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

public class PfCast<I extends IntRing<I>, R extends IntRing<R>> extends IntFunction<I, R> {

    public PfCast(final ImmutableList<? extends IntegerDomain<I>> domains, final IntegerDomain<R> resultDomain) {
        super(PredefinedFunction.Func.Cast, domains, false);
        this.resultDomain = resultDomain;
    }

    @Override
    protected IntegerDomain<R> determineResultDomain() {
        return null;
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Wild;
    }

    @Override
    public ITerm<R> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        // FIXME: as soon as we get restricted integers

//        final IntegerDomain fromDomain = domains.get(0);
//        final BigInt bi =
//            PredefinedUtil.getIntValue(t.get(0), fromDomain);
//        if (bi == null) {
//            return null;
//        } else {
//            final IntegerDomain targetDomain = domains.get(1);
//            return PredefinedSemanticsFactory.createInt(
//                BigInt.create(targetDomain.sign(targetDomain.castUnsigned(fromDomain.unsign(bi)))),
//                targetDomain).getTerm();
//        }

        throw new UnsupportedOperationException("FIXME");
    }

}
