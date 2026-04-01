/**
 * @author nowonder
 * @version $Id$
 */

package aprove.strategies.Util;

/**
 * Take exceptions and collect them in a buffer.
 * @author nowonder
 */
public class StringExceptionLogger implements ExceptionLogger {
    /**
     * A string buffer to store the exceptions in.
     */
    private StringBuilder buffer = new StringBuilder();

    /**
     * Log the given exception.
     * @param e Some exception.
     */
    @Override
    public void log(final Throwable e) {
        this.buffer.append(e);
        this.buffer.append("\n");
        for (StackTraceElement elem : e.getStackTrace()) {
            this.buffer.append("\tat ");
            this.buffer.append(elem);
            this.buffer.append("\n");
        }
    }

    @Override
    public String toString() {
        return this.buffer.toString();
    }

}
