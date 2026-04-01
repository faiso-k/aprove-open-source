package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.Heuristics.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Allow non-natural coefficients?
 *
 * @author fuhs
 * @version $Id$
 */
public interface RatHeuristic {

    /**
     * Inner enum whose values will be useful for ParameterManager.
     */
    public enum Heuristic {
        FULLRAT,
        PAPER;

        /**
         * @param h
         * @return a corresponding *fresh* RatHeuristic (which you can
         *  equip with obligation-dependent data)
         */
        public static RatHeuristic getRatHeuristic(Heuristic h) {
            switch (h) {
            case FULLRAT: return new AlwaysRat();
            case PAPER: return new PaperRat();
            default: throw new RuntimeException("Heuristic " + h +
                        " not integrated yet.");
            }
        }
    }

    /**
     * Returns whether we are allowed to use rational coeffs at all.
     *
     * @param f
     * @return whether we are allowed to use rational coeffs at all
     */
    public abstract boolean allowRat();


    /**
     * Returns whether we are allowed to use rational coeffs for
     * some arg position of f.
     *
     * @param f
     * @return whether we are allowed to use rational coeffs for
     *  some arg position of f.
     */
    public abstract boolean allowRat(FunctionSymbol f);

    /**
     * Returns whether we are allowed to use rational coeffs for
     * arg position i of f.
     *
     * @param f
     * @return whether we are allowed to use rational coeffs for
     *  arg position i of f.
     */
    public abstract boolean allowRatCoeff(FunctionSymbol f, int i);

    /**
     * Returns whether we are allowed to use a rational constant
     * in the implementation of f.
     *
     * @param f
     * @return whether we are allowed to use a rational constant
     *  in the interpretation of f
     */
    public abstract boolean allowRatConst(FunctionSymbol f);

    /**
     * Sets the P and R components of a DP problem.
     *
     * @param p
     * @param r
     */
    public abstract void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r);
}
