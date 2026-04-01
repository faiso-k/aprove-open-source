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

public class PfBwnot extends IntFunction {

    public PfBwnot(ImmutableList<? extends IntegerDomain> domains) {
        super(PredefinedFunction.Func.Bwnot, domains, false);
    }

    @Override
    public boolean isBitwise() {
        return true;
    }

    @Override
    public TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        BigInteger bi = PredefinedSemanticsFactory.getIntValue(t.get(0), this.domains.get(0));
        if (bi == null) {
            return null;
        } else {
            return PredefinedUtil.createInt(bi.not());
        }
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Wild;
    }

    @Override
    protected Domain determineResultDomain() {
        return this.domains.get(0);
    }

}
