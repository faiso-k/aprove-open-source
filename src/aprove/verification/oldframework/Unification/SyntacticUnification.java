package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *  Unification algorithm for syntatic unification.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class SyntacticUnification extends GeneralUnification {

    /** Returns a set containing an mgu of s and t if they are unifyable,
     * returns an empty set otherwise.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    List<AlgebraSubstitution> res = new Vector<AlgebraSubstitution>();
        Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
    V.addAll(t.getVars());

    try {
        res.add(ElementaryUnification.baseAway(s.unifies(t), V, W));
    }
    catch(UnificationException e) {
    }

    return res;
    }

    @Override
    public boolean areUnifiable(AlgebraTerm s, AlgebraTerm t) {
    return s.isUnifiable(t);
    }

    @Override
    public boolean matchable(AlgebraTerm s, AlgebraTerm t) {
        return s.isMatchable(t);
    }

    @Override
    public Collection<AlgebraSubstitution> match(AlgebraTerm s, AlgebraTerm t) {
        List<AlgebraSubstitution> res = new Vector<AlgebraSubstitution>();
        try {
            res.add(s.matches(t));
        } catch (UnificationException e) {
        }
        return res;
    }


}
