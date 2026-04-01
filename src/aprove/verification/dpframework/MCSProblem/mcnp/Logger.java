package aprove.verification.dpframework.MCSProblem.mcnp;

/**
 * Deprecated! Please use a {@link java.util.logging.Logger}.
 */
@Deprecated
public enum Logger {
    ;

    private static final String LOGGER_NAME = "aprove.verification.dpframework.MCSProblem.mcnp.Logger";
    private static final java.util.logging.Logger LOGGER = java.util.logging.Logger.getLogger(LOGGER_NAME);

    public static void writeDebug(String message) {
        if (Config.isLogDebug()) {
            LOGGER.finer(message);
        }
    }

    public static void write(String message) {
        if (Config.isLogOutput()) {
            LOGGER.fine(message);
        }
    }

    public static void writeReport(String message) {
        if (Config.isLogReport()) {
            LOGGER.info(message);
        }
    }

    public static void writeError(String message) {
        LOGGER.severe(message);
    }

    public static void writeWarning(String message) {
        LOGGER.warning(message);
    }
}
