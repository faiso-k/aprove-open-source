package aprove.verification.oldframework.Bytecode.Merger;
/**
 * A TooExpensiveException is thrown when it is too expensive to merge two
 * states (because some better result is already known).
 * @author cotto
 */
public class TooExpensiveException extends Exception {

    private final String description;

    public TooExpensiveException(final String desc) {
        this.description = desc;
    }

    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = 4695907678548446985L;

    @Override
    public String toString() {
        return this.description;
    }

    /**
     * We do not need the stack trace, so we override the costly method.
     * @return null
     */
    @Override
    public synchronized Throwable fillInStackTrace() {
        return null;
    }
}
