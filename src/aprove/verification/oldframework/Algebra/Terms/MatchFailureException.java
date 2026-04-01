package aprove.verification.oldframework.Algebra.Terms;

/** Exception thrown by matching and unification algorithms in Term class.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class MatchFailureException extends UnificationException {

    public MatchFailureException(String s, AlgebraTerm l, AlgebraTerm r) {
        super(s, l, r, null,null);
    }

}
