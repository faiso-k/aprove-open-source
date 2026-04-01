/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public abstract class IntFunction<I extends IntRing<I>, R extends SemiRing<R>> extends PredefinedFunction<I, R> {

    protected IntFunction(final PredefinedFunction.Func func,
            final ImmutableList<? extends IntegerDomain<I>> domains,
            final boolean identicalDomains) {
        super(func, domains);
        if (identicalDomains && Globals.useAssertions) {
            assert (PredefinedSemanticsFactory.checkSameIntDomains(domains) != null) : "domains must be identical";
        }
    }

    @Override
    public boolean canMatchPredefLhs(final ITerm<?> t) {
        if (t.isVariable()) {
            return true;
        } else {
            final IFunctionApplication<?> f = (IFunctionApplication<?>) t;
            if (!this.equals(f.getRootSymbol().getSemantics())) {
                return false;
            }
            final List<ITerm<?>> arguments = f.getArguments();

            for (int i = arguments.size() - 1; i >= 0; i--) {
                final ITerm<?> arg = arguments.get(i);
                if (!arg.isVariable()) {
                    final IFunctionSymbol<?> fs =
                        ((IFunctionApplication<?>) arg).getRootSymbol();
                    if (!PredefinedUtil.isInt(fs, this.domains.get(i))) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    public ImmutableSet<UnconditionalIRule> getFiniteRuleSet(final IFunctionSymbol<R> fs) {
        return null;
    }

    @Override
    public PredefinedFunction.Func getFunc() {
        return this.func;
    }

    @Override
    public boolean hasFiniteRuleSet() {
        return false;
    }

    @Override
    public boolean isPredefLhs(final ITerm<?> t) {
        if (t.isVariable()) {
            return false;
        } else {
            final IFunctionApplication<?> f = (IFunctionApplication<?>) t;
            if (!this.equals(f.getRootSymbol().getSemantics())) {
                return false;
            }
            final List<ITerm<?>> arguments = f.getArguments();
            for (int i = arguments.size() - 1; i >= 0; i--) {
                final ITerm<?> arg = arguments.get(i);
                if (arg.isVariable()) {
                    return false;
                } else {
                    final IFunctionSymbol<?> fs =
                        ((IFunctionApplication<?>) arg).getRootSymbol();
                    if (!PredefinedUtil.isInt(fs, this.domains.get(i))) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

}
