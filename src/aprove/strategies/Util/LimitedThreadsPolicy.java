package aprove.strategies.Util;

import java.util.*;

/**
 * Implements a threading policy where never more than N threads are working on
 * your jobs. Commonly used with N==1 for debugging.
 */
public class LimitedThreadsPolicy implements ThreadingPolicy {
    // Class invariant: either credits or queue.size() will be 0 at all times.
    // If credits is nonzero, new requested workers are started instantly (using up a credit).
    // If credits is zero, new workers are queued until a finished worker returns a credit.

    private int credits;
    private final Queue<Runnable> queue = new LinkedList<>();

    /**
     * Constructs a new queuing policy that downgrades into singlethreading: One
     * job will be executed at a time (although different jobs may be executed
     * in different workers). Equivalent to
     * <code>new LimitedThreadsPolicy(1)</code>
     */
    public LimitedThreadsPolicy() {
        this(1);
    }

    /**
     * Constructs a new policy where the given number of threads will be active
     * at most, at any time.
     */
    public LimitedThreadsPolicy(final int numThreads) {
        this.credits = numThreads;
    }

    @Override
    public void schedule(final Runnable task) {
        this.obtainCredit(new LimitedRunner(task));
    }

    private synchronized void obtainCredit(final Runnable task) {
        if (this.credits > 0) {
            this.credits -= 1;
            PrioritizableThreadPool.INSTANCE.executeNow(task);
        } else {
            this.queue.add(task);
        }
    }

    synchronized void returnCredit() {
        if (this.queue.isEmpty()) {
            this.credits += 1;
        } else {
            final Runnable newTask = this.queue.remove();
            PrioritizableThreadPool.INSTANCE.executeNow(newTask);
        }
    }

    private class LimitedRunner implements Runnable {
        private final Runnable wrapped;

        public LimitedRunner(final Runnable task) {
            this.wrapped = task;
        }

        @Override
        public void run() {
            try {
                this.wrapped.run();
            } finally {
                LimitedThreadsPolicy.this.returnCredit();
            }
        }

        @Override
        public String toString() {
            return "L:" + this.wrapped.toString();
        }

    }
}
