package aprove.verification.dpframework.PATRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Static function computing the equivalence class of a term.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public final class EquivalenceClassGenerator {

    /**
     * Computes the equivalence class of t.  E needs to be collapse-free and i.u.v.
     */
    public static Set<TRSTerm> getEquivalenceClass(TRSTerm t, Set<Equation> E) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        Set<TRSTerm> todo = new LinkedHashSet<TRSTerm>();
        Set<TRSTerm> newterms;

        todo.add(t);

        while (!todo.isEmpty()) {
            TRSTerm s = todo.iterator().next();
            todo.remove(s);
            res.add(s);
            newterms = EquivalenceClassGenerator.getAll(s, E);
            newterms.removeAll(res);
            todo.addAll(newterms);
        }

        return res;
    }

    private static Set<TRSTerm> getAll(TRSTerm s, Set<Equation> E) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();

        res.addAll(s.rewrite(EquivalenceClassGenerator.getRfromE(E)));
        res.addAll(s.rewrite(EquivalenceClassGenerator.getRfromE(EquivalenceClassGenerator.invert(E))));

        return res;
    }

    private static Map<FunctionSymbol, Set<Rule>> getRfromE(Set<Equation> E) {
        Map<FunctionSymbol, Set<Rule>> res = new LinkedHashMap<FunctionSymbol, Set<Rule>>();

        for (Equation e : E) {
            TRSFunctionApplication l = (TRSFunctionApplication) e.getLeft();
            FunctionSymbol f = l.getRootSymbol();
            Set<Rule> resf = res.get(f);
            if (resf == null) {
                resf = new LinkedHashSet<Rule>();
                res.put(f, resf);
            }
            resf.add(Rule.create(l, e.getRight()));
        }

        return res;
    }

    private static Set<Equation> invert(Set<Equation> E) {
        Set<Equation> res = new LinkedHashSet<Equation>();

        for (Equation e : E) {
            res.add(Equation.create(e.getRight(), e.getLeft()));
        }

        return res;
    }

}
