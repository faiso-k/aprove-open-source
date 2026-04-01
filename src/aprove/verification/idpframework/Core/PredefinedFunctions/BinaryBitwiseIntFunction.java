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

public abstract class BinaryBitwiseIntFunction<I extends IntRing<I>> extends IntFunction<I, I> {

    public BinaryBitwiseIntFunction(final PredefinedFunction.Func func,
            final ImmutableList<? extends IntegerDomain<I>> domains) {
        super(func, domains, true);
    }

    @Override
    protected IntegerDomain<I> determineResultDomain() {
        final IntegerDomain<I> dom0 = (IntegerDomain<I>) this.domains.get(0);
        final IntegerDomain<I> dom1 = (IntegerDomain<I>) this.domains.get(1);
        if (dom0.getBits() == 0) {
            return dom0;
        } else if (dom1.getBits() == 1) {
            return dom1;
        } else if (dom0.getBits() > dom1.getBits()) {
            return dom0;
        } else {
            return dom1;
        }
    }

    /**
     * Evaluate integer expression (according to the rules of
     * <code>evaluate</code>)
     * <p>
     * This method can (and should be) implemented to operate over unrestricted
     * (mathematical) integers. Domain range check and cast_unsigned are already
     * taken care of.
     * </p>
     * <p>
     * <em>Note</em>: This means all parameters are non-null and (for restricted
     * k-bit integers) in the range <code>-2^(k-1)</code> to\
     * <code>2^(k-1)-1</code>.
     * </p>
     * @param predefinedMap TODO
     */
    protected abstract ITerm<I> intEvaluate(I bi1,
        I bi2, IDPPredefinedMap predefinedMap);

    @Override
    public boolean isBitwise() {
        return true;
    }

    @Override
    public ITerm<I> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        final I bi1 =
            PredefinedUtil.getIntValue(t.get(0), this.domains.get(0));
        if (bi1 == null) {
            return null;
        }

        final I bi2 =
            PredefinedUtil.getIntValue(t.get(1), this.domains.get(1));

        if (bi2 == null) {
            return null;
        }

        return this.intEvaluate(bi1, bi2, predefinedMap);
    }

}
