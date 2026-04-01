package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Logic.Formulas.*;

/** Interface for formula sources.
 *  <P>
 *  Implement by extending with interfaces.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface FormulaSource {

    /** Returns a formula from this source.
     * @return Formula from this source.
     * @see Formula
     */
    public Formula getFormula();

}
