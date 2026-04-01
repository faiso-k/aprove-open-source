package aprove.verification.dpframework.MCSProblem.satsolver;

public interface SATSolver {

    /**
     * @param dimacsFilename path to a CNF file in Dimacs format
     * @return null if satisfiability of the SAT instance in
     *  <code>dimacsFilename</code> could not be shown; if satisfiability
     *  of the SAT instance is shown, an array is returned where an entry
     *  -i denotes that the variable i is assigned to false and an entry
     *  i denotes that the variable i is assigned to true (note that the
     *  <i>position</i> of the entry in the array is arbitrary)
     * @throws SATSolverException if the SAT solver terminated without showing
     *  satisfiability or unsatisfiability (i.e., it crashed)
     */
    public int[] solveFile(String dimacsFilename) throws SATSolverException;
}
