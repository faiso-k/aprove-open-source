package aprove.verification.dpframework.PATRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Static functions computing various CS related things.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public final class CSTermHelper {

    /**
     * Computes the active subterms of t.
     */
    public static Set<TRSTerm> getActiveSubterms(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        CSTermHelper.getActiveSubterms(t, mu, res);
        return res;
    }

    private static void getActiveSubterms(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu, Set<TRSTerm> accu) {
        accu.add(t);
        if (!t.isVariable()) {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            int arr = f.getArity();
            ImmutableSet<Integer> muEntry = mu.get(f.getName());
            for (int i = 0; i < arr; i++) {
                if (muEntry.contains(Integer.valueOf(i))) {
                    CSTermHelper.getActiveSubterms(ft.getArgument(i), mu, accu);
                }
            }
        }
    }

    /**
     * Computes the active variables of t.
     */
    public static Set<TRSVariable> getActiveVariables(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSVariable> res = new LinkedHashSet<TRSVariable>();
        CSTermHelper.getActiveVariables(t, mu, res);
        return res;
    }

    private static void getActiveVariables(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu, Set<TRSVariable> accu) {
        if (t.isVariable()) {
            accu.add((TRSVariable) t);
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            int arr = f.getArity();
            ImmutableSet<Integer> muEntry = mu.get(f.getName());
            for (int i = 0; i < arr; i++) {
                if (muEntry.contains(Integer.valueOf(i))) {
                    CSTermHelper.getActiveVariables(ft.getArgument(i), mu, accu);
                }
            }
        }
    }

    /**
     * Computes the inactive subterms of t.
     */
    public static Set<TRSTerm> getInactiveSubterms(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        CSTermHelper.getInactiveSubterms(t, mu, res);
        return res;
    }

    private static void getInactiveSubterms(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu, Set<TRSTerm> accu) {
        if (!t.isVariable()) {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            int arr = f.getArity();
            ImmutableSet<Integer> muEntry = mu.get(f.getName());
            for (int i = 0; i < arr; i++) {
                if (muEntry.contains(Integer.valueOf(i))) {
                    CSTermHelper.getInactiveSubterms(ft.getArgument(i), mu, accu);
                } else {
                    accu.addAll(ft.getArgument(i).getSubTerms());
                }
            }
        }
    }

    /**
     * Computes the inactive variables of t.
     */
    public static Set<TRSVariable> getInactiveVariables(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSVariable> res = new LinkedHashSet<TRSVariable>();
        CSTermHelper.getInactiveVariables(t, mu, res);
        return res;
    }

    private static void getInactiveVariables(TRSTerm t, ImmutableMap<String, ImmutableSet<Integer>> mu, Set<TRSVariable> accu) {
        if (!t.isVariable()) {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            int arr = f.getArity();
            ImmutableSet<Integer> muEntry = mu.get(f.getName());
            for (int i = 0; i < arr; i++) {
                if (muEntry.contains(Integer.valueOf(i))) {
                    CSTermHelper.getInactiveVariables(ft.getArgument(i), mu, accu);
                } else {
                    accu.addAll(ft.getArgument(i).getVariables());
                }
            }
        }
    }

}
