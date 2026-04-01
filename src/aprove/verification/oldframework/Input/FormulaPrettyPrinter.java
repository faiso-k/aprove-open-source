package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Logic.Formulas.*;

/** Interface for formula prettyprinters.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface FormulaPrettyPrinter {

    /** Returns a prettyprinted string representation
     *  of the given formula.
     * @param form Formula to prettyprint.
     * @return Prettyprinted string representation of the given formula.
     */
    public String prettyPrint(Formula form);

}
