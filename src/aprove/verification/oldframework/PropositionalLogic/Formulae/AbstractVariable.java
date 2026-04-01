package aprove.verification.oldframework.PropositionalLogic.Formulae;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * We still need to distinguish whether the atomic proposition
 * that is not a Boolean constant is a (Boolean) variable or an
 * atomic proposition over some theory. In both cases, the
 * truth value of the Formula is not predetermined even if you
 * know the truth values of all children.
 *
 * This gives rise to this abstract class.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractVariable<T> extends Atom<T> {

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    @Override
    public boolean isLiteral() {
        return true;
    }

    @Override
    public int getGateType() {
        throw new UnsupportedOperationException("Implementors of AbstractVariable do not have a gate type!");
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return cache.evaluate(this);
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {
        cache.assertValue(this, one);
    }
}
