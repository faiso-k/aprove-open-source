package aprove.verification.oldframework.PropositionalLogic.Formulae;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * A formula which has a junctor of arity >= 1 at its root.
 *
 * (Note to non-German speakers: "Junktor" is the German word for
 * "Boolean connective". The word "junctor" does exist in English,
 * but has a rather different meaning -- it's a "false friend".)
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class JunctorFormula<T> extends AbstractFormula<T> {

    @Override
    public int getId() {
        int result = this.id;
        if ((result == AbstractFormula.ID_UNSET) && (this.gate != null)) {
            return this.gate.output;
        }
        return result;
    }

    @Override
    public boolean isAtomic() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    /**
     * @return the String representation of the junctor
     */
    public abstract String getJunctor();

}
