package aprove.verification.oldframework.IntTRS;

import java.util.concurrent.*;
import java.util.logging.*;

/**
 * Deprecated! Please use a {@link java.util.logging.Logger}.
 */
@Deprecated
public final class DebugLogger {

    public static DebugLogger getLogger(String name) {
        return LOGGERS.computeIfAbsent(name, k -> new DebugLogger(getJavaLogger(name)));
    }

    private static Logger getJavaLogger(String name) {
        return Logger.getLogger("aprove.verification.oldframework.IntTRS.DebugLogger." + name);
    }

    public static void finishLog(String name) {
        LOGGERS.remove(name);
    }

    private static final ConcurrentHashMap<String, DebugLogger> LOGGERS = new ConcurrentHashMap<>();

    private final Logger logger;

    private DebugLogger(Logger logger) {
        this.logger = logger;
        this.log("Current thread id is " + Thread.currentThread().getId() + ".\n\n");
    }

    public void log(String message) {
        logger.fine(message);
    }

    public void log(Object o) {
        this.log(String.valueOf(o));
    }

    public void logln(String message) {
        this.log(message + "\n");
    }

    public void logln(Object o) {
        this.logln(String.valueOf(o));
    }

    public void logln() {
        this.log("\n");
    }
}
