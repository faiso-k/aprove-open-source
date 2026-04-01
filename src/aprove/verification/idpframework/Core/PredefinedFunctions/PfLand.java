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

public class PfLand extends BooleanFunction {

    private volatile ImmutableSet<UnconditionalIRule> finiteRuleSet;

    private final static PredefinedFunction.Func func =
        PredefinedFunction.Func.Land;

    public PfLand(final ImmutableList<? extends BooleanDomain> domains) {
        super(PfLand.func, domains);
    }

    @Override
    public Boolean boolEvaluate(final ArrayList<? extends ITerm<?>> t) {
        for (final ITerm<?> arg : t) {
            final Boolean b = PredefinedUtil.getBoolValue(arg);
            if (b == null) {
                return null;
            } else if (!b.booleanValue()) {
                return Boolean.FALSE;
            }
        }

        return Boolean.TRUE;
    }

    @Override
    public IDependence filterPositon(final int i) {
        return IDependence.Incr;
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
                        new LinkedHashSet<UnconditionalIRule>(4);
                    ArrayList<ITerm<?>> args;

                    args = new ArrayList<ITerm<?>>(2);
                    args.add(tru);
                    args.add(tru);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), tru));

                    args = new ArrayList<ITerm<?>>(2);
                    args.add(tru);
                    args.add(fals);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), fals));

                    args = new ArrayList<ITerm<?>>(2);
                    args.add(fals);
                    args.add(tru);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), fals));

                    args = new ArrayList<ITerm<?>>(2);
                    args.add(fals);
                    args.add(fals);
                    rules.add(IRuleFactory.create(
                        ITerm.createFunctionApplication(fs,
                            ImmutableCreator.create(args)), fals));

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

}
