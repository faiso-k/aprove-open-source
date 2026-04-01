package aprove.verification.oldframework.IntegerReasoning;

/**
 * Exception for division by zero.
 * @author cryingshadow
 * @version $Id$
 */
public class DivisionByZeroException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 8942854791541119425L;

    /**
     * Exception with default message.
     */
    public DivisionByZeroException() {
        super("Division by zero detected!");
    }

    /**
     * @param message The message.
     */
    public DivisionByZeroException(String message) {
        super(message);
    }

    /**
     * @param message The message.
     * @param cause The cause.
     */
    public DivisionByZeroException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * @param cause The cause.
     */
    public DivisionByZeroException(Throwable cause) {
        super(cause);
    }

}
