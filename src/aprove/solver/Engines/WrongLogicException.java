package aprove.solver.Engines;

/**
 * This exception is thrown we want to solve some formula in a specified logic,
 * but the solver detects that the formula is not in that logic (e.g. Q_LIA is
 * set, but we run yices with a nonlinear formula).
 * @author cotto
 */
public class WrongLogicException extends Exception {
    /**
     * Some UID.
     */
    private static final long serialVersionUID = -2759391171913339753L;

    /**
     * A descriptive error message.
     */
    private final String errorMessage;

    /**
     * A new exception with a specific error message.
     * @param errorMessageParam an error message
     */
    public WrongLogicException(final String errorMessageParam) {
        this.errorMessage = errorMessageParam;
    }

    /**
     * @return the error message
     */
    public String getErrorMessage() {
        return this.errorMessage;
    }
}
