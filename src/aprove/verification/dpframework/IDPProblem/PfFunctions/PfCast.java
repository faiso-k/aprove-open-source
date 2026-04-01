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

public class PfCast extends IntFunction {

    public PfCast(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Cast, domains, false);
    }

    @Override
    public TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        IntegerDomain fromDomain = this.domains.get(0);
        BigInteger bi = PredefinedSemanticsFactory.getIntValue(t.get(0), fromDomain);
        if (bi == null) {
            return null;
        } else {
            IntegerDomain targetDomain = this.domains.get(1);
            return PredefinedUtil.createInt(targetDomain.sign(targetDomain.castUnsigned(fromDomain.unsign(bi))));
        }
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }

    @Override
    protected Domain determineResultDomain() {
        return this.domains.get(1);
    }

}
