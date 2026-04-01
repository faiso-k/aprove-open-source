package aprove.strategies.Util;

/**
 * Thrown when the ParameterManager notices something is wrong due to errors
 * in strategy, property files, or (processor) annotations.
 *
 * When catching this exception, you should not print a stack trace
 * as it will not help. Instead, this exception is guaranteed to be thrown
 * with a message fully describing the problem.
 */
public class UserErrorException extends ParameterManagerException {
    private static final long serialVersionUID = 1L;

    public UserErrorException(String msg) {
        super(msg, null);
    }

    @Override
    protected void appendUserTrace(StringBuilder buf) {
        buf.append(this.getMessage());
    }
}