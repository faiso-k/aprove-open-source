package aprove.strategies.Abortions;

/**
 * Common superclass for classes that track CPU time of some kind of
 * calculation.
 */
public interface TimeTracker {
    /**
     * Called periodically by the TimeRefresherThread,
     * when we are scheduled to receive periodic polls.
     */
    public void checkTime();

    /**
     * Kills whatever is being tracked as soon and as hard as possible.
     *
     * Not for casual use.
     */
    public void kill();
}
