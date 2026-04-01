package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Heuristic for SAT checking. Takes a SAT formula and decides by the
 * size of the formula if it should be solved with MiniSAT or with SAT4J.
 *
 * @author Andreas Kelle-Emden
 */
public class HeuristicMiniSATChecker implements SATChecker {

    private static MiniSATFileChecker minisatChecker = new MiniSATFileChecker(2, false, false, true, false, false, false, false, false, false);
    private static SAT4JChecker       sat4jChecker   = new SAT4JChecker();

    private int limit;

    public HeuristicMiniSATChecker(int limit) {
        this.limit = limit;
    }

    // TODO We do never call this method. Why the heck do we have it?
    @Override
    public void setAssumps(Set<Formula<None>> assumps) {
    }
    // TODO look above.
    @Override
    public int[] solveCNF(Formula<None> formula, Abortion aborter) {
        return null;
    }

    @Override
    public int[] solve(Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {
        //long formulaLength = formula.label(1);
        int formulaLength = formula.label(1);
        //System.err.println("formulaLength is: " + formulaLength);
        if (formulaLength <= this.limit) {
            return HeuristicMiniSATChecker.sat4jChecker.solve(formula, aborter);
        } else {
            return HeuristicMiniSATChecker.minisatChecker.solve(formula, aborter);
        }
    }

    @Override
    public int[] solve(String dimacs, Abortion aborter)
            throws AbortionException, SolverException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not usable on heuristic MiniSAT checker");
    }
}
