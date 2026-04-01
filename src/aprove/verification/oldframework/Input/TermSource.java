package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Interface for term sources.
 *  <P>
 *  Implement by extending with interfaces.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface TermSource {

    /** Returns a term from this source.
     * @return term from this source.
     * @see AlgebraTerm
     */
    public AlgebraTerm getTerm();

}
