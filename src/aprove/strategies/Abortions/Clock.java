package aprove.strategies.Abortions;

/**
 * Tracks CPU time used up by calculations.
 *
 * Used to allow strategy to abort calculations based on CPU time usage,
 * which is widely regarded to be more predictable than wall time.
 *
 * A Clock keeps a maximum time set when it was created, and as soon as
 * it passes that time, it notifies its listener.
 * This is guaranteed to happen at most once.
 */
public class Clock {
    private static ClockListener DUMMY_LISTENER =
            new ClockListener() {
                @Override
                public void ring(Clock source) {
                    // Do nothing.
                }
            };

    private long curMillis = 0;
    private final long maxMillis;
    private ClockListener listener;

    /**
     * Creates a new clock with the specified maximum time and listener.
     */
    public Clock(long maxMillis, ClockListener listener) {
        this.maxMillis = maxMillis;
        this.listener = listener != null ? listener : Clock.DUMMY_LISTENER;
    }

    /**
     * Creates a new clock that never rings.
     *
     * Useful to track CPU time but not limit it.
     */
    public Clock() {
        this(Long.MAX_VALUE, Clock.DUMMY_LISTENER);
    }

    /**
     * If it is impossible or inconvenient for you to set the listener
     * on construction, you can pass null and invoke this method later.
     *
     * Be aware that it gives you an obvious small race condition.
     */
    public synchronized void setListener(ClockListener listener) {
        this.listener = listener;
    }

    /**
     * Returns the time used by calculations tracked by this clock.
     * May continue to increase after this clock rang, if calculations
     * do not stop using CPU time immediately.
     *
     * Thus, this method may be used to get realistic cost estimates.
     */
    public synchronized long getMillisUsed() {
        return this.curMillis;
    }

    /**
     * Called by Tracker implementations whenever they note the time
     * used by the calculation they track has increased.
     */
    void increaseTime(long millis) {
        if (millis < 0) {
            throw new IllegalArgumentException("time increase was negative");
        }

        // These booleans help ensure that we only ring once.
        boolean wasBelow, isAbove;

        synchronized(this) {
            wasBelow = (this.curMillis < this.maxMillis);
            this.curMillis += millis;
            isAbove = (this.curMillis >= this.maxMillis);
        }

        if (wasBelow && isAbove) {
            this.listener.ring(this);
        }
    }
}
