package aprove.strategies.Abortions;

/**
 * Implement this to be notified by a clock when it rings.
 */
public interface ClockListener {
    /**
     * Called by a clock when it rings.
     *
     * Called at most once by any one clock, but called from an arbitrary thread.
     *
     * Be careful about shared state, and return quickly.
     */
    public void ring(Clock source);
}
