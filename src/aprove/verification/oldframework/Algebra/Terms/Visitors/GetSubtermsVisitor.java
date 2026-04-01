package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Return all subterms of a term.
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */

public class GetSubtermsVisitor extends CoarseGrainedDepthFirstTermVisitor<AlgebraTerm> {

    protected Vector<AlgebraTerm> set;

    @Override
    public void inVariable(AlgebraVariable v) {
        this.set.add(v);
    }

    @Override
    public void inFunctionApp(AlgebraFunctionApplication f) {
        this.set.add(f);
    }

    protected GetSubtermsVisitor() {
        this.set = new Vector<AlgebraTerm>();
    }

    /** Returns a set of terms containing all subterms of this term
     *  including the term itself.
     */
    public static List<AlgebraTerm> apply(AlgebraTerm t) {
    GetSubtermsVisitor v = new GetSubtermsVisitor();
    t.apply(v);
    return v.set;
    }

    /** Returns a set of terms containing
     *    all subterms of this term, not including the term itself.
     */
    public static List<AlgebraTerm> applyProper(AlgebraTerm t) {
        List<AlgebraTerm> set = GetSubtermsVisitor.apply(t);
        set.remove(t);
        return set;
    }

}
