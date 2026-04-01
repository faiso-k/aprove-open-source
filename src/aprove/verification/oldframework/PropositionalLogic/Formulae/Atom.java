package aprove.verification.oldframework.PropositionalLogic.Formulae;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Atoms are variables or the boolean constants 0 and 1.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class Atom<T> extends AbstractFormula<T> {

    @Override
    public boolean isAtomic() {
        return true;
    }

    @Override
    public int countSub() {
        return 1;
    }
}
