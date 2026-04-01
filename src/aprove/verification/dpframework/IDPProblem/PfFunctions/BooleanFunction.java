/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public abstract class BooleanFunction extends PredefinedFunction<BooleanDomain> {

    protected BooleanFunction(PredefinedFunction.Func func, ImmutableList<? extends BooleanDomain> domains) {
        super(func, domains);
    }

    @Override
    public boolean isBoolean() {
        return true;
    }

    @Override
    protected TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        Boolean res = this.boolEvaluate(t);
        if (res != null) {
            return PredefinedSemanticsFactory.getBoolean(res).getTerm();
        } else {
            return null;
        }
    }

    protected abstract Boolean boolEvaluate(List<? extends TRSTerm> t);

    @Override
    public boolean canMatchPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap) {
        if (this.func.getArity() == 0) {
            // we have no rules
            return false;
        }
        if (t.isVariable()) {
            return true;
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            if (!this.equals(predefinedMap.getPredefinedSemantics(f.getRootSymbol()))) {
                return false;
            }
            for (TRSTerm arg : f.getArguments()) {
                if (!arg.isVariable()) {
                    FunctionSymbol fs = ((TRSFunctionApplication)arg).getRootSymbol();
                    if (PredefinedSemanticsFactory.getBoolean(fs) == null) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    public boolean isPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap) {
        if (this.func.getArity() == 0) {
            // we have no rules
            return false;
        }
        if (t.isVariable()) {
            return false;
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            if (!this.equals(predefinedMap.getPredefinedSemantics(f.getRootSymbol()))) {
                return false;
            }
            for (TRSTerm arg : f.getArguments()) {
                if (arg.isVariable()) {
                    return false;
                } else {
                    FunctionSymbol fs = ((TRSFunctionApplication)arg).getRootSymbol();
                    if (PredefinedSemanticsFactory.getBoolean(fs) == null) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    protected Domain determineResultDomain() {
        return DomainFactory.BOOLEAN;
    }

}
