package aprove.verification.oldframework.Bytecode.Parser.Exceptions;

/**
 * Something went wrong while parsing a .class file.
 * @author cotto
 */
public abstract class ClassParseException extends Exception {
    /**
     * A unique ID.
     */
    private static final long serialVersionUID = -6267636807414865844L;

    /**
     * The reason for this exception.
     */
    private final String reason;

    /**
     * Create a new exception with the given reason.
     * @param reasonParam the reason for this exception.
     */
    public ClassParseException(final String reasonParam) {
        this.reason = reasonParam;
    }

    /**
     * @return the reason of this exception as a string.
     */
    @Override
    public String toString() {
        return this.reason;
    }
}
