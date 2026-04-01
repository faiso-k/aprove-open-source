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
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import immutables.*;

public class PfUnaryMinus extends IntFunction {

    public PfUnaryMinus(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.UnaryMinus, domains, false);
    }

    @Override
    public boolean isArithmetic() {
        return true;
    }

    @Override
    public TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        BigInteger bi = PredefinedSemanticsFactory.getIntValue(t.get(0), this.domains.get(0));
        if (bi == null) {
            return null;
        } else {
            return PredefinedUtil.createInt(bi.negate());
        }
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Decr;
    }

    @Override
    protected Domain determineResultDomain() {
        return this.domains.get(0);
    }

}
