package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Utility.*;

/**
 *  Abstract class of an unification algorithm for elementary unification, i.e.
 *  the unification problem contains only variables and the function symbols
 *  occuring in the equations.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public abstract class ElementaryUnification implements java.io.Serializable{

    /** Returns a (preferably minimal) complete collection (preferably a set) of unifiers of the terms away
     * from V(s, t).
     * @param s  a term
     * @param t  another term
     * @see #unify(Term, Term, Set<Variable>)
     */
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t) {
    Set<AlgebraVariable> W = new HashSet<AlgebraVariable>(s.getVars());
    W.addAll(t.getVars());
    return this.unify(s, t, W);
    }

    /** Returns a (preferably minimal) complete set of unifiers of the terms away from
     * from W >= V(s, t), i.e. for all substitutions sub that are returned,
     * (1) DOM(sub) = V(s, t)
     * (2) VRAN(sub) /\ W = {}
     * @param s  a term
     * @param t  another term
     */
    public abstract Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W);

    /** Determines weather two terms are unifiable modulo this theory.
     * The default implementation might not be what you want!
     */
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    return !this.unify(s, t).isEmpty();
    }

    /** Determines weather two terms are unifiable.
     * The default implementation might not be what you want!
     */
    public boolean areUnifiable(AlgebraTerm s, AlgebraTerm t) {
    if(s.isUnifiable(t)) {
        /* already syntactically */
        return true;
    }
    return this.areTheoryUnifiable(s, t);
    }

    /** Base sub away from W >= V.
     */
    public static AlgebraSubstitution baseAway(AlgebraSubstitution sub, Set<AlgebraVariable> V, Set<AlgebraVariable> W) {
    AlgebraSubstitution subby = sub.deepcopy();

    /* extend sub to have V as domain */
    Set<AlgebraVariable> todo = new HashSet<AlgebraVariable>(V);
        todo.removeAll(sub.getTermDomain());

    Iterator i = todo.iterator();
    while(i.hasNext()) {
        AlgebraVariable v = (AlgebraVariable)i.next();
        subby.put(v.getVariableSymbol(), v);
    }

    todo = new HashSet<AlgebraVariable>(subby.getRangeVariables());
    /* only keep forbidden variables */
    todo.retainAll(W);
    i = todo.iterator();

    /* rename away from W */
    FreshVarGenerator vargen = new FreshVarGenerator(W);
    AlgebraSubstitution ren = AlgebraSubstitution.create();

    while(i.hasNext()) {
        AlgebraVariable v = (AlgebraVariable)i.next();
        AlgebraVariable w = vargen.getFreshVariable(v, true);
        ren.put(v.getVariableSymbol(), w);
    }

    return subby.compose(ren);
    }

}
