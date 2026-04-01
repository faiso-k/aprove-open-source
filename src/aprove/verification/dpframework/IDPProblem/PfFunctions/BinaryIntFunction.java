/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import immutables.*;

public abstract class BinaryIntFunction extends IntFunction {

    public BinaryIntFunction(PredefinedFunction.Func func, ImmutableList<? extends IntegerDomain> domains, boolean identicalDomains) {
        super(func, domains, identicalDomains);
    }

    @Override
    public boolean isArithmetic() {
        return true;
    }

    @Override
    public TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        BigInteger bi1 = PredefinedSemanticsFactory.getIntValue(t.get(0), this.domains.get(0));
        if (bi1 == null) {
            return null;
        }

        BigInteger bi2 = PredefinedSemanticsFactory.getIntValue(t.get(1), this.domains.get(1));
        if (bi2 == null) {
            return null;
        }

        return PredefinedUtil.createInt(this.intEvaluate(bi1, bi2));
    }

    /**
     * Evaluate integer expression (according to the rules of
     * <code>evaluate</code>)
     *
     * <p>This method can (and should be) implemented to operate over
     * unrestricted (mathematical) integers. Domain range check, sign, unsign,
     * cast_unsigned are already taken care of.</p>
     *
     * <p><em>Note</em>: This means all parameters are non-null and (for
     * restricted k-bit integers) in the range <code>-2^k</code> to\
     * <code>2^k-1</code>.</p>
     */
    protected abstract BigInteger intEvaluate(BigInteger val1, BigInteger val2);

    @Override
    protected Domain determineResultDomain() {
        return this.domains.get(0);
    }

}
