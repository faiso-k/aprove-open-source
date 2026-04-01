package aprove.api.decisions;

/**
 * Indicates that an error occurred while creating the {@link ProblemDecisions}.
 */
public class ProblemDecisionsInstantiationException extends Exception {

    public ProblemDecisionsInstantiationException() {
        super();
    }

    public ProblemDecisionsInstantiationException(String message, Throwable cause) {
        super(message, cause);
    }

    public ProblemDecisionsInstantiationException(String message) {
        super(message);
    }

    public ProblemDecisionsInstantiationException(Throwable cause) {
        super(cause);
    }
}
