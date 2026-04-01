package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.InterHeuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Wrapper to make sure that the used heuristic for polynomials with
 * negative coefficients of variables only allows negative coefficients
 * for non-mu-replacing argument positions. (If mu-reduction pairs or
 * dependency pairs for context-sensitive rewriting are not your thing,
 * you probably don't want to use this class.)
 *
 * @author fuhs
 * @version $Id$
 */
public class CSNCHeuristicWrapper implements NCInterHeuristic {

    // used for non-mu-repl. positions
    private NCInterHeuristic actualHeuristic;
    private ReplacementMap mu;

    public CSNCHeuristicWrapper() {
        this.actualHeuristic = null;
        this.mu = null;
    }

    /**
     * @param actualHeuristic the actualHeuristic to set
     */
    public void setActualHeuristic(NCInterHeuristic actualHeuristic) {
        if (Globals.useAssertions) {
            // non-termination, anyone?
            assert actualHeuristic != this;
        }
        this.actualHeuristic = actualHeuristic;
    }

    public void setMu(ReplacementMap mu) {
        this.mu = mu;
    }

    @Override
    public void setP(Set<? extends GeneralizedRule> p) {
        this.actualHeuristic.setP(p);

    }

    @Override
    public void setR(Map<? extends GeneralizedRule, QActiveCondition> r) {
        this.actualHeuristic.setR(r);

    }

    /**
     * Allows negative coeffs for the args of f only if it is okay for all
     * arg positions (and if the actual heuristic agrees).
     *
     * @param f
     * @return whether negative coeffs are allowed when interpreting f
     */
    @Override
    public boolean useNegCoeff(FunctionSymbol f) {
        ImmutableSet<Integer> muOfF = this.mu.getMap().get(f);
        if (Globals.useAssertions) {
            assert muOfF != null;
            for (int j : muOfF) {
                assert j >= 0;
                assert j < f.getArity();
            }
        }
        boolean result = false;
        if (muOfF.size() == 0) {
            // if not asked for a specific arg position, allow neg coeffs only
            // if it is okay for all arg positions (and only if the actual
            // heuristic agrees)
            result = this.actualHeuristic.useNegCoeff(f);
        }
        return result;
    }

    /**
     * Allows negative coeffs for the i-th arg of f only if i \notin mu(f)
     * (i.e., if mu blocks mu-rewrite steps below the i-th arg of f) and,
     * of course, only if the actual heuristic agrees.
     *
     * @param f
     * @param i - an arg position of f
     * @return whether neg coeffs are allowed for x_i in f_Pol
     */
    @Override
    public boolean useNegCoeff(FunctionSymbol f, int i) {
        Set<Integer> muOfF = this.mu.getMap().get(f);
        if (Globals.useAssertions) {
            int n = f.getArity();
            assert i >= 0;
            assert i < n;
            assert muOfF != null;
            for (int j : muOfF) {
                assert j >= 0;
                assert j < n;
            }
        }
        boolean result = false;
        if (! muOfF.contains(i)) {
            // we require mu-monotonicity => neg. coeffs only for
            // non-rewritable arg positions
            result = this.actualHeuristic.useNegCoeff(f, i);
        }
        return result;
    }

    /**
     * Allows negative constants iff the internal heuristic does,
     * mu does not matter here since weak monotonicity is not affected
     * in any case.
     *
     * @param f
     * @return whether a neg constant is allowed in f_Pol
     */
    @Override
    public boolean useNegConst(FunctionSymbol f) {
        return this.actualHeuristic.useNegConst(f);
    }

}
