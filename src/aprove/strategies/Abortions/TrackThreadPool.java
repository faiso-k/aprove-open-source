package aprove.strategies.Abortions;

class TrackThreadPool extends TrackThread {
    private final PooledJob runner;
    private volatile Thread thread = null;

    /**
     * Method for {@link PooledJob}.
     *
     * Should not be called by anyone else!
     */
    static TrackThreadPool createAndStart(final Abortion abortion, final PooledJob runner) {
        final TrackThreadPool result = new TrackThreadPool(abortion, runner);
        result.start();
        return result;
    }

    private TrackThreadPool(final Abortion abortion, final PooledJob runner) {
        super(abortion);
        this.runner = runner;
    }

    void startTrackingMe() {
        this.thread = Thread.currentThread();
        this.checkTime();
    }

    void stopTracking() {
        this.checkTime();
        this.deregisterWithAbortion();
        this.thread = null;
        TimeRefresher.deregister(this);
    }

    @Override
    protected Thread getThread() {
        return this.thread;
    }

    @Override
    public void kill() {
        this.runner.kill();
    }
}
