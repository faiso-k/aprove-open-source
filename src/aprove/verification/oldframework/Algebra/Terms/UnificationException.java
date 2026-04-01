package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

/** Exception thrown by matching and unification algorithms in Term class.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public abstract class UnificationException extends Exception {

    protected AlgebraTerm l, r;
    protected Set<PairOfTerms> set;
    protected AlgebraSubstitution subs;

    public UnificationException(String s, AlgebraTerm l, AlgebraTerm r, AlgebraSubstitution subs, Set<PairOfTerms> set) {
        super(s);
        this.l = l;
        this.r = r;
    this.subs = subs;
    this.set = set;
    }

    public AlgebraTerm getLeft() {
        return this.l;
    }

    public AlgebraTerm getRight() {
        return this.r;
    }

    public AlgebraSubstitution getSubstitution() {
        return this.subs;
    }

    public Set<PairOfTerms> getSetOfPairOfTerms() {
        return this.set;
    }

}
