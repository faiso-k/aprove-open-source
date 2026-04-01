package aprove.strategies.Util;


public abstract class ParameterManagerException extends Exception {
    private static final long serialVersionUID = 1L;

    public ParameterManagerException(String message, Throwable cause) {
        super(message, cause);
    }

    public ParameterManagerException(String message) {
        super(message, null);
    }

    public ParameterManagerException(Throwable cause) {
        super(cause);
    }

    protected abstract void appendUserTrace(StringBuilder buf);

    public String getUserTrace() {
        StringBuilder buf = new StringBuilder();
        this.appendUserTrace(buf);
        return buf.toString();
    }
}
