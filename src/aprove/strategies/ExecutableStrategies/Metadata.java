package aprove.strategies.ExecutableStrategies;

/**
 * Enum containing all keys valid for RuntimeInformation.getMetadata().
 *
 * Generally, a given Metadata item cannot be assumed to exist,
 * even when it should probably exist.
 *
 * When you need more items, feel free to add stuff here.
 */
public enum Metadata {
    /**
     * Maps to Boolean.TRUE only if the input was a real .srs file.
     *
     * Needed to produce "correct" proofs in COLOR mode
     */
    IS_SRS,

    /**
     * Exists in metadata (mapped to non-null) if we know
     * nonterm will not be interesting in this project.
     *
     * This is a dreadful hack, and should eventually be moved into problem metadata.
     */
    AVOID_NONTERM,

    /**
     * Sometimes maps to the filename of the problem file (?)
     */
    PROBLEM_PATH_NAME,

    /**
     * May contain an ExceptionLogger that should be used for uncaught processor exceptions
     */
    EXCEPTION_LOGGER;
}
