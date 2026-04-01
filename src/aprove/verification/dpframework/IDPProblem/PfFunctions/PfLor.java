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

public class PfLor extends BooleanFunction {

    private final static PredefinedFunction.Func func =
        PredefinedFunction.Func.Lor;

    private ImmutableSet<GeneralizedRule> finiteRuleSet;

    public PfLor(ImmutableList<? extends BooleanDomain> domains) {
        super(PfLor.func, domains);
    }

    @Override
    public Boolean boolEvaluate(List<? extends TRSTerm> t) {
        for (TRSTerm arg : t) {
            Boolean b = PredefinedSemanticsFactory.getBoolValue(arg);
            if (b == null) {
                return null;
            } else if (b.booleanValue()) {
                return Boolean.TRUE;
            }
        }

        return Boolean.FALSE;
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

                    args = new ArrayList<TRSTerm>(2);
                    args.add(tru);
                    args.add(tru);
                    rules.add(GeneralizedRule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), tru));

                    args = new ArrayList<TRSTerm>(2);
                    args.add(tru);
                    args.add(fals);
                    rules.add(GeneralizedRule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), tru));

                    args = new ArrayList<TRSTerm>(2);
                    args.add(fals);
                    args.add(tru);
                    rules.add(GeneralizedRule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), tru));

                    args = new ArrayList<TRSTerm>(2);
                    args.add(fals);
                    args.add(fals);
                    rules.add(GeneralizedRule.create(TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(args)), fals));

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
        return IDependence.Incr;
    }

}

