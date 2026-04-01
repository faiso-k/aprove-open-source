package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

/** Exception thrown by matching and unification algorithms in Term class.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class SymbolClashException extends UnificationException {

    public SymbolClashException(String s, AlgebraTerm l, AlgebraTerm r, AlgebraSubstitution subs, Set<PairOfTerms> set) {
        super(s, l, r, subs, set);
    }

}
