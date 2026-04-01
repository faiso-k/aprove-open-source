package aprove.strategies.Util;

import java.util.*;

/**
 * Implements a ThreadingPolicy where at least N threads are running at any
 * time, more if resources allow it. So this implementation normally submits
 * tasks with low priority, but whenever less than a predefined number of its
 * tasks are currently executing, it will start more with priority.
 */
public class LimitedPriorityPolicy implements ThreadingPolicy {

    /**
     * When we go below this number of threads, we can start more with priority.
     */
    private final int permittedPrioThreads;
    /** The number of threads we currently have executing */
    private int runningThreads;

    /**
     * Contains all tasks we submitted with low priority and may re-submit with
     * high priority if one of the previous high-priority tasks finishes
     */
    private final Queue<LimitedPriorityWrapper> tasks = new LinkedList<>();

    /**
     * Constructs a new instance of this policy.
     * @param permittedPriorityThreads - this number of threads will always be
     * run
     */
    public LimitedPriorityPolicy(final int permittedPriorityThreads) {
        this.permittedPrioThreads = permittedPriorityThreads;
    }

    @Override
    public synchronized void schedule(final Runnable task) {
        final LimitedPriorityWrapper wrappedTask = new LimitedPriorityWrapper(task);
        if (this.permittedPrioThreads > this.runningThreads) {
            this.prioritize(wrappedTask);
        } else {
            this.tasks.add(wrappedTask);
            PrioritizableThreadPool.INSTANCE.execute(wrappedTask);
        }
    }

    synchronized void maybeStartMoreThreads() {
        while (this.permittedPrioThreads > this.runningThreads && !this.tasks.isEmpty()) {
            final LimitedPriorityWrapper wrap = this.tasks.remove();
            this.prioritize(wrap);
        }
    }

    /**
     * Schedules a task with priority, if it is not already running. Call with
     * lock held!
     */
    private void prioritize(final LimitedPriorityWrapper task) {
        if (!task.prioIfNotRunning()) {
            // Already running? Okay, nevermind then.
            return;
        }

        // This thread will soon occupy a slot, so count it already.
        // compare code in LimitedPriorityWrapper.run()
        this.runningThreads++;
        PrioritizableThreadPool.INSTANCE.executeNow(task);
    }

    private class LimitedPriorityWrapper implements Runnable {
        private final Runnable wrapped;
        private boolean priority;
        private boolean started = false;

        public LimitedPriorityWrapper(final Runnable wrapped) {
            this.wrapped = wrapped;
        }

        boolean prioIfNotRunning() {
            synchronized (LimitedPriorityPolicy.this) {
                if (!this.started) {
                    this.priority = true;
                }

                return !this.started;
            }
        }

        @Override
        public void run() {
            synchronized (LimitedPriorityPolicy.this) {
                if (this.started) {
                    return;
                }
                this.started = true;
                // Otherwise, it's been previously counted.
                if (!this.priority) {
                    LimitedPriorityPolicy.this.runningThreads++;
                }
            }

            try {
                this.wrapped.run();

            } finally {
                synchronized (LimitedPriorityPolicy.this) {
                    LimitedPriorityPolicy.this.runningThreads--;
                    LimitedPriorityPolicy.this.maybeStartMoreThreads();
                }
            }
        }
    }
}
