package aprove.api.decisions;

/**
 * Indicates that an invalid decision was made.
 */
public class InvalidDecisionException extends IllegalArgumentException {

    public InvalidDecisionException() {
        super();
    }

    public InvalidDecisionException(String message, Throwable cause) {
        super(message, cause);
    }

    public InvalidDecisionException(String message) {
        super(message);
    }

    public InvalidDecisionException(Throwable cause) {
        super(cause);
    }
}
