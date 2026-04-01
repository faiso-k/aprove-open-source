package aprove.strategies.Util;


public class WrappedParamMgrException extends ParameterManagerException {
    private static final long serialVersionUID = 1L;

    public WrappedParamMgrException(String message, ParameterManagerException cause) {
        super(message, cause);
    }

    @Override
    protected void appendUserTrace(StringBuilder buf) {
        buf.append(this.getMessage());
        buf.append('\n');
        ((ParameterManagerException) this.getCause()).appendUserTrace(buf);
    }
}
