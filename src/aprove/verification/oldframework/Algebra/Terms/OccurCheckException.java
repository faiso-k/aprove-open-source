package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

/** Exception thrown by matching and unification algorithms in Term class.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class OccurCheckException extends UnificationException {

    public OccurCheckException(String s, AlgebraTerm l, AlgebraTerm r, AlgebraSubstitution subs, Set<PairOfTerms> set) {
        super(s, l, r, subs, set);
    }

}
