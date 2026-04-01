package aprove.strategies.Util;

import java.util.*;

/**
 * Simple policy that ensures fair queuing. When multiple instances of this
 * class are used to submit new jobs, slots will be assigned round-robin between
 * the instances. The jobs submitted to one instance of this class will still be
 * executed in a FIFO manner, of course. This is achieved as follows: We simply
 * wait until a submitted-to-ThreadPool task starts executing before we submit
 * another task to the ThreadPool. This effectively puts tasks at the back of
 * the queue each time. Note that for this to work, the threadpool has to be
 * sufficiently loaded to actually queue new requests.
 */
public class FairQueuingPolicy implements ThreadingPolicy {
    private final Queue<Runnable> queuedForSubmit = new LinkedList<>();
    private boolean hasScheduledTask = false;
    private final ThreadingPolicy outerPolicy;

    /**
     * Execute a new task as soon as the previous task from this queue is
     * finished.
     */
    public FairQueuingPolicy() {
        this.outerPolicy = null;
    }

    /**
     * Enqueue a new task in the given queue as soon as the previous task from
     * this queue is finished.
     * @param outerPolicy
     */
    public FairQueuingPolicy(final ThreadingPolicy outerPolicy) {
        this.outerPolicy = outerPolicy;
    }

    @Override
    public synchronized void schedule(final Runnable task) {
        if (this.hasScheduledTask) {
            this.queuedForSubmit.add(task);
        } else {
            this.submit(task);
        }
    }

    private void submit(final Runnable task) {
        if (this.outerPolicy == null) {
            PrioritizableThreadPool.INSTANCE.execute(new FairWrapper(task));
        } else {
            this.outerPolicy.schedule(new FairWrapper(task));
        }
        this.hasScheduledTask = true;
    }

    synchronized void slotTicked() {
        final Runnable task = this.queuedForSubmit.poll();
        if (task == null) {
            this.hasScheduledTask = false;
        } else {
            this.submit(task);
        }
    }

    private class FairWrapper implements Runnable {
        private final Runnable wrapped;

        public FairWrapper(final Runnable wrapped) {
            this.wrapped = wrapped;
        }

        @Override
        public void run() {
            FairQueuingPolicy.this.slotTicked();
            this.wrapped.run();
        }

        @Override
        public String toString() {
            return "F:" + this.wrapped.toString();
        }
    }
}
