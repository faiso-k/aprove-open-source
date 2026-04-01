package aprove.verification.idpframework.Core.Utility;

import java.util.logging.*;

/**
 *
 * @author MP
 */
public class TimeLogger {

    private static Logger log = Logger.getLogger("aprove.verification.idpframework.Core.Utility.TimeLogger");

    private final String description;
    private final Level level;
    private final long startTime;

    private final long threshold;

    public TimeLogger(final String description, final Level level, final long threshold) {
        this.description = description;
        this.level = level;
        this.threshold = threshold;
        this.startTime = System.currentTimeMillis();
    }

    public void log(final Object comment) {
        final long executionTime = System.currentTimeMillis() - this.startTime;
        if (executionTime > this.threshold) {
            TimeLogger.log.log(this.level, this.description + " " + executionTime + " ms" + (comment != null ? ", " + comment.toString() : ""));
        }
    }

    public void log() {
        this.log(null);
    }

}
