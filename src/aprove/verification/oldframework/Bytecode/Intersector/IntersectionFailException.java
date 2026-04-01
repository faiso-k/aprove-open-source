package aprove.verification.oldframework.Bytecode.Intersector;


/**
 * @author cotto
 */
public class IntersectionFailException extends Exception {

    /**
     * Just some random ID.
     */
    private static final long serialVersionUID = -8394119153107024615L;

    /**
     * The reason for failing the intersection.
     */
    private final String reason;

    /**
     * @param r the reason for failing the intersection.
     */
    public IntersectionFailException(final String r) {
        this.reason = r;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.reason;
    }
}
