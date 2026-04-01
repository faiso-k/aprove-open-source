/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public abstract class IntFunction extends PredefinedFunction<IntegerDomain> {


    protected IntFunction(PredefinedFunction.Func func, ImmutableList<? extends IntegerDomain> domains, boolean identicalDomains) {
        super(func, domains);
        if (identicalDomains && Globals.useAssertions) {
            assert(PredefinedSemanticsFactory.checkSameIntDomains(domains) != null) : "domains must be identical";
        }
    }

    @Override
    public PredefinedFunction.Func getFunc() {
        return this.func;
    }

    @Override
    public boolean canMatchPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            return true;
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            if (!this.equals(predefinedMap.getPredefinedSemantics(f.getRootSymbol()))) {
                return false;
            }
            List<TRSTerm> arguments =  f.getArguments();
            for (int i = arguments.size()-1; i>=0; i--) {
                TRSTerm arg = arguments.get(i);
                if (!arg.isVariable()) {
                    FunctionSymbol fs = ((TRSFunctionApplication)arg).getRootSymbol();
                    if (!predefinedMap.isInt(fs, this.domains.get(i))) {
                        return false;
                    }
                }
            }
            return true;
        }
    }


    @Override
    public boolean isPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            return false;
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            if (!this.equals(predefinedMap.getPredefinedSemantics(f.getRootSymbol()))) {
                return false;
            }
            List<TRSTerm> arguments =  f.getArguments();
            for (int i = arguments.size()-1; i>=0; i--) {
                TRSTerm arg = arguments.get(i);
                if (arg.isVariable()) {
                    return false;
                } else {
                    FunctionSymbol fs = ((TRSFunctionApplication)arg).getRootSymbol();
                    if (!predefinedMap.isInt(fs, this.domains.get(i))) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    public boolean hasFiniteRuleSet() {
        return false;
    }

    @Override
    public ImmutableSet<GeneralizedRule> getFiniteRuleSet(FunctionSymbol fs) {
        return null;
    }

}
