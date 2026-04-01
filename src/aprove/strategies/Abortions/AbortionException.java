/*
 * Created on 13.04.2005
 */
package aprove.strategies.Abortions;

public final class AbortionException extends RuntimeException {
    private static final long serialVersionUID = 1L;

    public AbortionException(final String reason) {
        super(reason);
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
