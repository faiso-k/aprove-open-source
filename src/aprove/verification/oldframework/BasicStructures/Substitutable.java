package aprove.verification.oldframework.BasicStructures;

import java.util.*;

/**
 * Variables in substitutable objects can be substituted by expressions.
 * @author cryingshadow
 * @version $Id$
 */
public interface Substitutable {

    /**
     * @param sigma Some substitution.
     * @return This object where all variables have been substituted according to the specified substitution
     *         simultaneously.
     */
    default Substitutable applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    /**
     * @param sigma Some substitution.
     * @return This object where all variables have been substituted according to the specified substitution
     *         simultaneously.
     */
    Substitutable applySubstitution(Substitution sigma);

    /**
     * @param v Some variable.
     * @param e Some expression.
     * @return This object where all occurrences of v have been replaced by e.
     */
    default Substitutable applySubstitution(Variable v, Expression e) {
        return this.applySubstitution(Collections.singletonMap(v, e));
    }

}
