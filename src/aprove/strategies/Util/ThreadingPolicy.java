package aprove.strategies.Util;

import aprove.runtime.*;

/**
 * Used by the framework to communicate how new work should be scheduled.
 */
public interface ThreadingPolicy {
    /** Default policy: Start everything NOW. */
    public ThreadingPolicy HIGH = new HighPolicy();
    /** Default policy: Put everything in a queue, try to avoid having more threads than CPUs */
    public ThreadingPolicy LOW = new LowPolicy();
    /** Default policy: Set by command line - acts like HIGH or LOW */
    public ThreadingPolicy DEFAULT = new DefaultPolicy();

    /**
     * Schedule execution of some task.
     * Depending on the policy, the task may not start until some resources are available.
     */
    public void schedule(Runnable task);


    class HighPolicy implements ThreadingPolicy {
        @Override
        public void schedule(Runnable runnable) {
            PrioritizableThreadPool.INSTANCE.executeNow(runnable);
        }
    }

    class LowPolicy implements ThreadingPolicy {
        @Override
        public void schedule(Runnable runnable) {
            PrioritizableThreadPool.INSTANCE.execute(runnable);
        }
    }

    class DefaultPolicy implements ThreadingPolicy {
        @Override
        public void schedule(Runnable task) {
            if (Options.defaultThreadingHasPriority) {
                ThreadingPolicy.HIGH.schedule(task);
            } else {
                ThreadingPolicy.LOW.schedule(task);
            }
        }
    }

}
