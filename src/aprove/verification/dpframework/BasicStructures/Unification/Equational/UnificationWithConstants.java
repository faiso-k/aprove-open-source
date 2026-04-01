/*
 * Created on Feb 9, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;
/**
 *  Abstract class of an unification algorithm for unification with constants, i.e.
 *  the unification problem contains only variables, additional (free) constants
 *  and the function symbols occuring in the equations.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public abstract class UnificationWithConstants extends ElementaryUnification {

    /** Returns whether s matches t, i.e. whether there is some substitution
     * sigma s.t. sigma(s)=t.
     */
    public boolean matchable(TRSTerm s, TRSTerm t) {
        return this.areUnifiable(s, UnificationWithConstants.fixVars(s, t));
    }

    /** Returns a (preferably minimal) complete collection (preferably a set) of matchers.
     * @param s  The pattern.
     * @param t  The term to be matched.
     */
    public Collection<TRSSubstitution> match(TRSTerm s, TRSTerm t) {
        return this.unify(s, UnificationWithConstants.fixVars(s, t));
    }

    /** Replaces the variables in t by fresh constants not occurring in s and t.
     */
    public static TRSTerm fixVars(TRSTerm s, TRSTerm t) {
        Set<FunctionSymbol> used = s.getFunctionSymbols();
        used.addAll(t.getFunctionSymbols());
        FreshNameGenerator fng = new FreshNameGenerator(used, FreshNameGenerator.TYPE_INFERENCE);
        Map<TRSVariable, TRSTerm> sub = new LinkedHashMap<TRSVariable, TRSTerm>();
        for(TRSVariable var : t.getVariables()) {
            FunctionSymbol cs = FunctionSymbol.create(fng.getFreshName("c", false), 0);
            TRSFunctionApplication ca = TRSTerm.createFunctionApplication(cs, TRSTerm.EMPTY_ARGS);
            sub.put(var, ca);
        }
        return t.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(sub)));
    }

}
