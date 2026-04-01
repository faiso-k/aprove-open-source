/*
 * Created on Feb 8, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import immutables.*;

/**
 *  Abstract class of an unification algorithm for elementary unification, i.e.
 *  the unification problem contains only variables and the function symbols
 *  occuring in the equations.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public abstract class ElementaryUnification{

    /** Returns a (preferably minimal) complete collection (preferably a set) of unifiers of the terms away
     * from V(s, t).
     * @param s  a term
     * @param t  another term
     * @see #unify(Term, Term, Set<Variable>)
     */
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t) {
        Set<TRSVariable> W = new HashSet<TRSVariable>(s.getVariables());
        W.addAll(t.getVariables());
        return this.unify(s, t, W);
    }

    /** Returns a (preferably minimal) complete set of unifiers of the terms away from
     * from W >= V(s, t), i.e. for all substitutions sub that are returned,
     * (1) DOM(sub) = V(s, t)
     * (2) VRAN(sub) /\ W = {}
     * @param s  a term
     * @param t  another term
     */
    public abstract Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W);

    /** Determines weather two terms are unifiable modulo this theory.
     * The default implementation might not be what you want!
     */
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        return !this.unify(s, t).isEmpty();
    }

    /** Determines weather two terms are unifiable.
     * The default implementation might not be what you want!
     */
    public boolean areUnifiable(TRSTerm s, TRSTerm t) {
        if(s.unifies(t)) {
            /* already syntactically */
            return true;
        }
        return this.areTheoryUnifiable(s, t);
    }

    /** Base sub away from W >= V.
     */
    public static TRSSubstitution baseAway(TRSSubstitution sub, Set<TRSVariable> V, Set<TRSVariable> W) {
        Map<TRSVariable,TRSTerm> smap = new LinkedHashMap<TRSVariable,TRSTerm>();

        /* extend sub to have V as domain */
        Set<TRSVariable> todo = new LinkedHashSet<TRSVariable>(V);
            todo.removeAll(sub.getDomain());

        for(TRSVariable v : todo) {
            smap.put(v, v);
        }

        TRSSubstitution subst = sub.extend(TRSSubstitution.create(ImmutableCreator.create(smap)));

        todo = new LinkedHashSet<TRSVariable>(subst.getVariablesInCodomain());
        /* only keep forbidden variables */
        todo.retainAll(W);

        /* rename away from W */
        FreshVarGenerator vargen = new FreshVarGenerator(W);
        Map<TRSVariable,TRSTerm> ren = new LinkedHashMap<TRSVariable,TRSTerm>();

        for(TRSVariable v : todo) {
            TRSVariable w = vargen.getFreshVariable(v, true);
            ren.put(v, w);
        }

        return subst.compose(TRSSubstitution.create(ImmutableCreator.create(ren)));
    }

}
