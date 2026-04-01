package aprove.verification.dpframework.MCSProblem.satsolver;

/**
 * To be thrown if SAT solving using an implementing class of
 * {@see SATSolver} terminates without a proper result.
 */
public class SATSolverException extends Exception {

    private static final long serialVersionUID = 1L;

    public SATSolverException(String reason) {
        super(reason);
    }

    public SATSolverException(Throwable reason) {
        super(reason);
    }
}
