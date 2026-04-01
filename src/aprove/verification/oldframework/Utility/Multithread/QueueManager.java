package aprove.verification.oldframework.Utility.Multithread;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Util.*;

/**
 * Queue manager. This class collects jobs and schedules them via the given scheduling policy.
 * The manager provides a method that waits until a job returns FINISH (possibly implicitly
 * by throwing an exception, see {@link #QueueManager(Abortion, WorkStatus)}) or
 * until all jobs have completed.
 *
 * The queue manager is mainly used by the {@link MultithreadedExecutor} class.
 * This class exposes a more detailed API that is mainly useful if your jobs
 * generate additional jobs during execution.
 *
 * @author Karsten Behrmann
 */
public class QueueManager<T extends AbortableRunnable> {
    private final Set<T> workers = new HashSet<>();
    private T haltReason = null;

    private ThreadingPolicy policy = ThreadingPolicy.DEFAULT;

    private final Abortion abortWhenDone;
    private final WorkStatus exceptionResult;

    /**
     * Equivalent to QueueManager(abortion, WorkStatus.CONTINUE).
     */
    public QueueManager(final Abortion abortion) throws AbortionException {
        this(abortion, WorkStatus.CONTINUE);
    }

    /**
     * Constructs a new queue manager for running a bunch of jobs.
     *
     * Set exceptionResult to WorkStatus.CONTINUE if an exception in a worker
     * is not a problem (i.e. when searching for solutions via different methods),
     * or to WorkStatus.FINISH if an exception in a worker should terminate the
     * entire queue (i.e. when processing some problems in parallel that all
     * need to be solved).
     *
     * In the latter case, use {@link #getHaltReason()} to distinguish if the queue
     * halted early or finished because all jobs were processed.
     *
     * @param abortion The abortion for CPU time accounting and stop control
     * @param exceptionResult If a worker terminates with an uncaught exception,
     * it will implicitly return with this status.
     * @throws AbortionException iff the abortion was already aborted before any work could be started
     */
    public QueueManager(final Abortion abortion, final WorkStatus exceptionResult) throws AbortionException {
        this.abortWhenDone = abortion.createChild();
        this.exceptionResult = exceptionResult;
    }

    public ThreadingPolicy getThreadingPolicy() {
        return this.policy;
    }

    public void setThreadingPolicy(final ThreadingPolicy policy) {
        this.policy = policy;
    }

    /**
     * Submits a new job for execution.
     *
     * The job is added to the tail of the queue.
     * This method can be called by worker threads, and will properly ensure
     * the new job is finished before a {@link #waitForAll()} returns.
     *
     * @throws AbortionException when the queue is already aborted, because
     * another job returned WorkStatus.FINISH, or a {@link #waitForAll()}
     * already returned.
     */
    public synchronized void add(final T job) throws AbortionException {
        this.abortWhenDone.checkAbortion();
        this.workers.add(job);
        this.policy.schedule(new AbortableWorker<>(job, this, this.abortWhenDone, this.exceptionResult));
    }

    /**
     * Submits a new job for execution using the given threading policy. The job
     * is added to the tail of the given queue. This method can be called by
     * worker threads, and will properly ensure the new job is finished before a
     * {@link #waitForAll()} returns. If no policy is given, the policy set for
     * this queue is used.
     * @throws AbortionException when the queue is already aborted, because
     * another job returned WorkStatus.FINISH, or a {@link #waitForAll()}
     * already returned.
     */
    public synchronized void add(final T job, final ThreadingPolicy policyParam) throws AbortionException {
        this.abortWhenDone.checkAbortion();
        this.workers.add(job);
        if (policyParam == null) {
            this.policy.schedule(new AbortableWorker<>(job, this, this.abortWhenDone, this.exceptionResult));
        } else {
            policyParam.schedule(new AbortableWorker<>(job, this, this.abortWhenDone, this.exceptionResult));
        }
    }

    /**
     * If this queue has halted because a worker returned FINISH, returns that worker.
     * Otherwise, returns null.
     *
     * The worker may have implicitly returned FINISH by throwing an exception,
     * if exceptionResult was set to FINISH in the constructor.
     *
     * Use this method to distinguish if all jobs completed, or if we halted early
     * because a job threw an exception / returned FINISH.
     *
     * @return null if this queue finished because all jobs completed, otherwise
     * the job that caused us to halt.
     */
    public synchronized T getHaltReason() {
        return this.haltReason;
    }

    /**
     * Waits until either all pending jobs are done,
     * or this queue is halted.
     */
    public void waitForAll() throws InterruptedException {
        PrioritizableThreadPool.INSTANCE.release();
        try {
            this.doWaitAll();
        } finally {
            // Don't hold lock here, to avoid deadlock
            PrioritizableThreadPool.INSTANCE.acquire();
        }
    }

    private synchronized void doWaitAll() throws InterruptedException {
        while (!this.workers.isEmpty()) {
            this.wait();
        }

        // At this point, fire abortion to be safe,
        // so no more jobs get submitted that we won't be waiting for
        this.abortWhenDone.abort("MultithreadedExecutor done waiting");
    }

    public void halt() {
        this.halt(null);
    }

    synchronized void halt(final T worker) {
        this.abortWhenDone.abort("MultithreadedExecutor halted");
        this.workers.clear();
        if (worker != null) {
            if (this.haltReason == null) {
                this.haltReason = worker;
            }
        }
        this.notifyAll();
    }

    synchronized void workDone(final T worker) {
        this.workers.remove(worker);
        this.notifyAll();
    }
}
