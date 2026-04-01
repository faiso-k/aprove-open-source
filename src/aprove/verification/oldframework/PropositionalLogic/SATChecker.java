package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public interface SATChecker {

    /**
     * SAT solving for arbitrary propositional formulae.
     *
     * Labels formula as a side effect, so do not reuse formula after
     * calling this method. If the corresponding FormulaFactory is
     * stateful (e.g., by caching constructed formulae), after calling
     * this method you should not use it any more to construct further
     * formulae.
     *
     * @param formula An unlabelled purely propositional formula
     *  not (necessarily) in CNF
     * @return An array of ints where -varid denotes false and varid denotes true
     */
    public int[] solve(Formula<None> formula, Abortion aborter) throws AbortionException, SolverException;

    /**
     * SAT solving for arbitrary preprocessed formulas.
     * @param dimacs A string representing a labelled formula
     * @return An array of ints where -varid denotes false and varid denotes true
     */
    public int[] solve(String dimacs, Abortion aborter) throws AbortionException, SolverException;

    /**
     * SAT solving for CNF formulae.
     * @param formula An unlabelled formula in CNF
     * @return An array of ints where -varid denotes false and varid denotes true
     */
    public int[] solveCNF(Formula<None> formula, Abortion aborter);

    /**
     * Assumptions are used by our modified minisat to try to solve the formula
     * given some heuristics. If this does not work, the solver will one-by-one drop assumptions
     * and solve the formula otherwise.
     * Other SAT-Checkers should quietly ignore this.
     * @param assumps The list of assumptions for the solver.
     * The last one (for loop) will be dropped first.
     */
    public void setAssumps(Set<Formula<None>> assumps);

}
