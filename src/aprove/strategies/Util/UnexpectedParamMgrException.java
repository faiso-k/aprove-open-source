package aprove.strategies.Util;

import java.io.*;

/**
 * Thrown by the ParameterManager when something went wrong.
 * Nothing specific about the failure is implied, maybe reflection failed,
 * maybe something else went wrong.
 *
 * The user should be presented with a stack trace when this is encountered.
 */
public class UnexpectedParamMgrException extends ParameterManagerException {
    private static final String FILTER_KEY = "Caused by: ";
    private static final long serialVersionUID = 1L;

    public UnexpectedParamMgrException(Exception e) {
        super(e);
    }

    @Override
    protected void appendUserTrace(StringBuilder buf) {
        buf.append("An unexpected exception was caught:\n");
        buf.append(this.filteredTrace());
    }

    private CharSequence filteredTrace() {
        /* A dirty trick to get a filtered stacktrace.
         * Our caller will be several layers of parameter manager,
         * which will be quite useless to the developer.
         *
         * So we let standard code give us a full stacktrace,
         * then cut off everything up to our actual cause.
         */

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        this.printStackTrace(pw);
        StringBuffer traceBuffer = sw.getBuffer();
        int cut = traceBuffer.indexOf(UnexpectedParamMgrException.FILTER_KEY);
        if (cut == -1) {
            return traceBuffer;
        }

        // Cut off up to name of cause, and strip trailing newline.
        return traceBuffer.subSequence(cut + UnexpectedParamMgrException.FILTER_KEY.length(),
                traceBuffer.length() - 1);
    }
}