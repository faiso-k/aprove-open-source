/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public abstract class BinaryIntRelation<I extends IntRing<I>> extends IntFunction<I, BooleanRing> {

    public BinaryIntRelation(final PredefinedFunction.Func func,
            final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(func, domains, true);
    }

    /**
     * Evaluate integer relation (according to the rules of
     * <code>evaluate</code>)
     * <p>
     * This method can (and should be) implemented to operate over unrestricted
     * (mathematical) integers. Domain range check is already taken care of.
     * </p>
     * <p>
     * <em>Note</em>: This means all parameters are non-null and (for restricted
     * k-bit integers) in the range <code>-2^(k-1)</code> to\
     * <code>2^(k-1)-1</code>.
     * </p>
     */
    protected abstract Boolean intBoolEvaluate(I bi1,
        I bi2);

    @Override
    public boolean isRelation() {
        return true;
    }

    @Override
    public ITerm<BooleanRing> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        final I bi1 =
            PredefinedUtil.getIntValue(t.get(0), this.domains.get(0));
        if (bi1 == null) {
            return null;
        }

        final I bi2 =
            PredefinedUtil.getIntValue(t.get(1), this.domains.get(0));

        if (bi2 == null) {
            return null;
        }

        return PredefinedSemanticsFactory.createBoolean(
            this.intBoolEvaluate(bi1, bi2)).getTerm();
    }

    @Override
    protected BooleanDomain determineResultDomain() {
        return DomainFactory.BOOLEANS;
    }

}
