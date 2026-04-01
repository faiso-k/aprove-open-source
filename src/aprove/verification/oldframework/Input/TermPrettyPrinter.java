package aprove.verification.oldframework.Input;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Interface for term prettyprinters.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public interface TermPrettyPrinter {

    /** Returns a prettyprinted string representation
     *  of the given term.
     * @param term Term to prettyprint.
     * @return Prettyprinted string representation of the given term.
     */
    public String prettyPrint(AlgebraTerm term);

}
