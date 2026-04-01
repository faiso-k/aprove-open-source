/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

public abstract class BooleanFunction extends PredefinedFunction<BooleanRing, BooleanRing> {

    protected BooleanFunction(final PredefinedFunction.Func func,
            final ImmutableList<? extends BooleanDomain> domains) {
        super(func, domains);
    }

    protected abstract Boolean boolEvaluate(ArrayList<? extends ITerm<?>> t);

    @Override
    public boolean canMatchPredefLhs(final ITerm<?> t) {
        if (this.func.getArity() == 0) {
            // we have no rules
            return false;
        }
        if (t.isVariable()) {
            return true;
        } else {
            final IFunctionApplication<?> f = (IFunctionApplication<?>) t;
            if (!this.equals(f.getRootSymbol().getSemantics())) {
                return false;
            }
            for (final ITerm<?> arg : f.getArguments()) {
                if (!arg.isVariable()) {
                    final IFunctionSymbol<?> fs =
                        ((IFunctionApplication<?>) arg).getRootSymbol();

                    if (fs.getSemantics() != PredefinedSemanticsFactory.BOOLEAN_FALSE
                        && fs.getSemantics() != PredefinedSemanticsFactory.BOOLEAN_TRUE) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    protected BooleanDomain determineResultDomain() {
        return DomainFactory.BOOLEANS;
    }

    @Override
    public boolean isBoolean() {
        return true;
    }

    @Override
    public boolean isPredefLhs(final ITerm<?> t) {
        if (this.func.getArity() == 0) {
            // we have no rules
            return false;
        }
        if (t.isVariable()) {
            return false;
        } else {
            final IFunctionApplication<?> f = (IFunctionApplication<?>) t;
            if (!this.equals(f.getRootSymbol().getSemantics())) {
                return false;
            }
            for (final ITerm<?> arg : f.getArguments()) {
                if (arg.isVariable()) {
                    return false;
                } else {
                    final IFunctionSymbol<?> fs =
                        ((IFunctionApplication<?>) arg).getRootSymbol();
                    if (fs.getSemantics() != PredefinedSemanticsFactory.BOOLEAN_FALSE
                        && fs.getSemantics() != PredefinedSemanticsFactory.BOOLEAN_TRUE) {
                        return false;
                    }
                }
            }
            return true;
        }
    }

    @Override
    protected ITerm<BooleanRing> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        final Boolean res = this.boolEvaluate(t);

        if (res != null) {
            return PredefinedSemanticsFactory.createBoolean(res).getTerm();
        } else {
            return null;
        }
    }

}
