package aprove.verification.oldframework.Utility.Multithread;

/**
 * Job status. Every finishing job has to return one of these values.
 */
public enum WorkStatus {
    /**
     * Continue work on the other items.
     */
    CONTINUE,
    /**
     * Abort other items as soon as possible
     * (useful both when you find the result you're looking for,
     * and when failure in one place means you cannot use any other results anymore.
     */
    FINISH
}