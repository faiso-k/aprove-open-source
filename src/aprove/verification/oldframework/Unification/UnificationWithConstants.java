package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

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
    public boolean matchable(AlgebraTerm s, AlgebraTerm t) {
    return this.areUnifiable(s, UnificationWithConstants.fixVars(s, t));
    }

    /** Returns a (preferably minimal) complete collection (preferably a set) of matchers.
     * @param s  The pattern.
     * @param t  The term to be matched.
     */
    public Collection<AlgebraSubstitution> match(AlgebraTerm s, AlgebraTerm t) {
        return this.unify(s, UnificationWithConstants.fixVars(s, t));
    }

    /** Replaces the variable in t by fresh constants not occuring in s and t.
     */
    public static AlgebraTerm fixVars(AlgebraTerm s, AlgebraTerm t) {
    Set<SyntacticFunctionSymbol> used = s.getFunctionSymbols();
    used.addAll(t.getFunctionSymbols());
    FreshNameGenerator fng = new FreshNameGenerator(used, FreshNameGenerator.TYPE_INFERENCE);
    Iterator i = t.getVars().iterator();
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    while(i.hasNext()) {
        AlgebraVariable var = (AlgebraVariable)i.next();
        ConstructorSymbol symb = ConstructorSymbol.create(fng.getFreshName("c", false), new Vector<Sort>(), var.getSort());
        sub.put((VariableSymbol)var.getSymbol(), ConstructorApp.create(symb));
    }
    return t.apply(sub);
    }

}
