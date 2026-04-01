/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public class PfLnot extends BooleanFunction {

    private final static PredefinedFunction.Func func =
        PredefinedFunction.Func.Lnot;
    private ImmutableSet<UnconditionalIRule> finiteRuleSet;

    public PfLnot(final ImmutableList<? extends BooleanDomain> domains) {
        super(PfLnot.func, domains);
    }

    @Override
    public Boolean boolEvaluate(final ArrayList<? extends ITerm<?>> t) {
        final ITerm<?> arg = t.get(0);
        final Boolean b = PredefinedUtil.getBoolValue(arg);

        if (b == null) {
            return null;
        } else {
            return Boolean.valueOf(!b.booleanValue());
        }
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Decr;
    }

    @Override
    public ImmutableSet<UnconditionalIRule> getFiniteRuleSet(final IFunctionSymbol<BooleanRing> fs) {
        if (this.finiteRuleSet == null) {
            synchronized (this) {
                if (this.finiteRuleSet == null) {
                    final IFunctionApplication<?> tru =
                        PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE;
                    final IFunctionApplication<?> fals =
                        PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE;

                    final Set<UnconditionalIRule> rules =
                        new LinkedHashSet<UnconditionalIRule>(2);
                    ArrayList<ITerm<?>> args;

                    args = new ArrayList<ITerm<?>>(1);
                    args.add(tru);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), fals));

                    args = new ArrayList<ITerm<?>>(1);
                    args.add(fals);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), tru));

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
    public boolean isBoolean() {
        return true;
    }

}
