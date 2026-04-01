package aprove.strategies.Abortions;

import java.util.*;
import java.util.logging.*;

public class TimeRefresher {
    // The number of milliseconds between refresh iterations
    public final static int REFRESH_INTERVAL = 100;

    private static final Logger log = Logger.getLogger(TimeRefresher.class.getName());
    private static final TimeRefresherThread THREAD;

    static {
        THREAD = new TimeRefresherThread();
        TimeRefresher.THREAD.start();
    }

    /**
     * Schedules a TimeTracker to have refreshTime() called periodically
     * by the TimeRefresherThread.
     */
    public static void register(TimeTracker tracker) {
        TimeRefresher.THREAD.add(tracker);
    }

    /**
     * Notifies us that we no longer need to call refreshTime() on the
     * passed TimeTracker.
     *
     * Note that immediate removal cannot be guaranteed, the TimeTracker
     * should be prepared to have refreshTime() called even after this
     * method returns.
     *
     * This method can be safely called even from inside refreshTime().
     */
    public static void deregister(TimeTracker tracker) {
        TimeRefresher.THREAD.remove(tracker);
    }

    private static class TimeRefresherThread extends Thread {
        private final Set<TimeTracker> pollSet = new LinkedHashSet<TimeTracker>();
        private final List<TimeTracker> added = new ArrayList<TimeTracker>();
        private final List<TimeTracker> removed = new ArrayList<TimeTracker>();

        private TimeRefresherThread() {
            super("TimeRefresherThread");
            this.setDaemon(true);
        }

        @Override
        public void run() {
            while(true) {
                try {
                    this.doPoll();
                    Thread.sleep(TimeRefresher.REFRESH_INTERVAL);
                } catch (InterruptedException e) {
                    return;
                } catch (Throwable th) {
                    TimeRefresher.log.log(Level.SEVERE, "Time refresher poll failed", th);
                }
            }
        }

        private void doPoll() {
            this.updatePollSet();
            for (TimeTracker tracker : this.pollSet) {
                tracker.checkTime();
            }
        }

        /* This method only gets called from doPoll().
         * This ensures we never modify pollSet concurrently
         * to the iteration in doPoll().
         *
         * Further, no locks are held while we call into other code.
         */
        private synchronized void updatePollSet() {
            this.pollSet.addAll(this.added);
            this.pollSet.removeAll(this.removed);
            this.added.clear();
            this.removed.clear();
        }

        synchronized void add(TimeTracker tracker) {
            this.added.add(tracker);
        }

        synchronized void remove(TimeTracker tracker) {
            this.removed.add(tracker);
        }
    }
}
