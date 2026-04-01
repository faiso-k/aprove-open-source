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

public class PfUnaryMinus<R extends IntRing<R>> extends IntFunction<R, R> {

    public PfUnaryMinus(final ImmutableList<? extends IntegerDomain<R>> domains) {
        super(PredefinedFunction.Func.UnaryMinus, domains, false);
    }

    @Override
    protected IntegerDomain<R> determineResultDomain() {
        return (IntegerDomain<R>) this.domains.get(0);
    }

    @Override
    public IDependence filterPositon(final int i) {
        switch (i) {
        case 0:
            return IDependence.Decr;
        default:
            throw new IllegalArgumentException();
        }
    }

    @Override
    public boolean isArithmetic() {
        return true;
    }

    @Override
    public ITerm<R> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        final R bi =
            PredefinedUtil.getIntValue(t.get(0), this.domains.get(0));
        if (bi == null) {
            return null;
        } else {
            return PredefinedSemanticsFactory.getIntTerm(
                bi.negate(), (IntegerDomain<R>) this.domains.get(0));
        }
    }

}
