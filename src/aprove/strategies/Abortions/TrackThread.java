package aprove.strategies.Abortions;

import java.lang.management.*;
import java.util.logging.*;

import aprove.*;

abstract class TrackThread extends AbortionListener implements TimeTracker {
    /*
     * Implementation note: Tricky code ahead, be careful.
     *
     * Basically, whenever checkTime() is called, we need to
     * figure out how much time was used since the last call,
     * and update accordingly.
     *
     * Pooled threads update time spontaneously (when they start up
     * and shut down), so we need to be prepared to have
     * checkTime() called from any thread.
     *
     * CPU time may be available or not, see getTimeIncrease().
     *
     * We may be tracking pooled threads (e.g. processors) or
     * custom threads (e.g. SAT4J). See subclasses.
     *
     * If our abortion fires, we need to give the threads some
     * grace time to die peacefully, and kill them if they do not
     * die by then. see all the kill methods.
     */

    private static final Logger log = Logger.getLogger(TrackThread.class.getName());
    protected static final ThreadMXBean BEAN = ManagementFactory.getThreadMXBean();
    protected static boolean cpuTimeSupported = TrackThread.isCpuTimeSupported();

    private static boolean isCpuTimeSupported() {
        if (Globals.aproveVersion != Globals.AproveVersion.DEVELOPER_VERSION) {
            return true;
        }

        try {
            if (TrackThread.BEAN.isThreadCpuTimeSupported()) {
                if (!TrackThread.BEAN.isThreadCpuTimeEnabled()) {
                    TrackThread.BEAN.setThreadCpuTimeEnabled(true);
                }
                return true;
            } else {
                TrackThread.log.severe("Platform claims not to support CPU time, falling back to wall time.");
                return false;
            }
        } catch (final UnsupportedOperationException e) {
            TrackThread.log.log(Level.SEVERE, "CPU time support detection failed, using wall time", e);
            return false;
        }
    }

    private static final int MIN_MILLIS_TO_STOP = 5000;

    private final Abortion abortion;
    private long lastMillis = -1;
    /**
     * Reflects if we are about to kill the target thread.
     * =0: Our abortion is not aborted yet
     * >0: The time (in millis) at which we will try to kill
     * <0: Thread has been killed.
     */
    private long killTime = 0;

    protected TrackThread(final Abortion abortion) {
        this.abortion = abortion;
        if (!TrackThread.cpuTimeSupported) {
            this.lastMillis = System.currentTimeMillis();
        }
    }

    protected void start() {
        this.abortion.addListenerOrFire(this);
        TimeRefresher.register(this);
    }

    /**
     * Returns the thread we are tracking, or null if the thread
     * is not available yet or anymore.
     *
     * Should not return different threads in different invocations,
     * otherwise our threadId cache field will break.
     *
     * If we know the thread has terminated, can call
     * TimeRefresher.deregister(this). Not before then, because
     * we rely on the TimeRefresher calls for kill scheduling.
     */
    protected abstract Thread getThread();

    /**
     * Kills the thread tracked by this, now. Use Thread.stop or some
     * similarly destructive-but-sure method.
     */
    @Override
    public abstract void kill();

    @Override
    public void checkTime() {
        final Thread runnerThread = this.getThread();
        if (runnerThread == null) {
            return;
        }

        /*
         * Only kill if we are checked from the outside. In the other case, we are ending this Thread right now.
         */
        if (!Thread.currentThread().equals(runnerThread)) {
            this.checkKill();
        }

        final long millis = this.getTimeIncrease(runnerThread);
        if (millis > 0) {
            this.abortion.increaseTime(millis);
        }
    }

    private synchronized long getTimeIncrease(final Thread runnerThread) {
        if (TrackThread.cpuTimeSupported) {
            return this.getCpuIncrease(runnerThread);
        } else {
            return this.getWallIncrease(runnerThread);
        }
    }

    private long getCpuIncrease(final Thread runnerThread) {
        final long threadId = runnerThread.getId();
        final long newNanos = TrackThread.BEAN.getThreadCpuTime(threadId);
        if (newNanos == -1) {
            return -1;
        }

        final long newMillis = newNanos / 1000000;
        long result = -1;

        if (this.lastMillis != -1) {
            result = newMillis - this.lastMillis;
        }
        this.lastMillis = newMillis;

        return result;
    }

    private long getWallIncrease(final Thread runnerThread) {
        long result = -1;
        final long currentTime = System.currentTimeMillis();
        if (runnerThread.getState() == Thread.State.RUNNABLE && this.lastMillis > 0) {
            result = currentTime - this.lastMillis;
        }
        this.lastMillis = currentTime;
        return result;
    }

    @Override
    public void abortionFired(final Abortion source, final String reason) {
        this.scheduleKill();
    }

    private synchronized void scheduleKill() {
        this.killTime = System.currentTimeMillis() + TrackThread.MIN_MILLIS_TO_STOP;
    }

    private void checkKill() {
        boolean doKill = false;
        synchronized (this) {
            if (this.killTime > 0 && System.currentTimeMillis() >= this.killTime) {
                doKill = true;
                this.killTime = -1;
            }
        }
        if (doKill) {
            this.kill();
            TimeRefresher.deregister(this);
        }
    }

    public static void logThreadStop(final Thread target, final String name) {
        TrackThread.log.warning("Running Thread.stop() against " + name + "\n");

        // make developers very aware of not only the fact /that/ a call to
        // aborter.checkAbortion() is missing, but also /where/ it is missing
        final Level level =
            Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION ? Level.WARNING : Level.INFO;
        if (!TrackThread.log.isLoggable(level)) {
            return;
        }
        TrackThread.log.log(level, "Stack trace:\n");
        final StackTraceElement[] stackTrace = target.getStackTrace();
        for (final StackTraceElement elem : stackTrace) {
            TrackThread.log.log(level, "    " + elem.toString() + "\n");
        }
    }
}
