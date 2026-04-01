/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class PfLnot extends BooleanFunction {

    private final static PredefinedFunction.Func func =
        PredefinedFunction.Func.Lnot;
    private ImmutableSet<GeneralizedRule> finiteRuleSet;

    public PfLnot(ImmutableList<? extends BooleanDomain> domains) {
        super(PfLnot.func, domains);
    }

    @Override
    public boolean isBoolean() {
        return true;
    }

    @Override
    public Boolean boolEvaluate(List<? extends TRSTerm> t) {
        TRSTerm arg = t.get(0);
        Boolean b = PredefinedSemanticsFactory.getBoolValue(arg);

        if (b == null) {
            return null;
        } else {
            return Boolean.valueOf(!b.booleanValue());
        }
    }

    @Override
    public ImmutableSet<GeneralizedRule> getFiniteRuleSet(FunctionSymbol fs) {
        if (this.finiteRuleSet == null) {
            synchronized(this) {
                if (this.finiteRuleSet == null) {
                    final TRSFunctionApplication tru = PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE;
                    final TRSFunctionApplication fals = PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE;

                    Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>(4);
                    ArrayList<TRSTerm> args;

                    args = new ArrayList<TRSTerm>(1);
                    args.add(tru);
                    rules.add(Rule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), fals));

                    args = new ArrayList<TRSTerm>(1);
                    args.add(fals);
                    rules.add(Rule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), tru));

                    this.finiteRuleSet = ImmutableCreator.create(rules);
                }
            }
        }
        return this.finiteRuleSet;
    }

    @Override
    public boolean hasFiniteRuleSet() {
        return true;
    }

    @Override
    public IDependence filterPositon(int i) {
        return IDependence.Decr;
    }

}
