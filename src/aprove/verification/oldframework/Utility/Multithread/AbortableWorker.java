package aprove.verification.oldframework.Utility.Multithread;

import aprove.strategies.Abortions.*;

/**
 * This class wraps a single job for use inside a queue manager.
 * This is necessary to keep the use of the multithreading framework correct.
 *
 * @author Karsten Behrmann
 */
class AbortableWorker<T extends AbortableRunnable> extends PooledJob {
    private WorkStatus result;

    private final T work;
    private final QueueManager<T> queue;
    private final Abortion aborter;

    public AbortableWorker(T work, QueueManager<T> queue, Abortion aborter, WorkStatus resultOnException) {
        super(aborter);
        this.work = work;
        this.queue = queue;
        this.aborter = aborter;
        // This field gets re-set at the end of wrappedRun(), unless we throw.
        this.result = resultOnException;
    }

    public T getWork() {
        return this.work;
    }

    @Override
    public String shortName() {
        return "MultithreadedExecutorRunner";
    }

    @Override
    protected void wrappedRun() throws AbortionException {
        this.aborter.checkAbortion();
        this.result = this.work.execute(this.aborter);
    }

    @Override
    protected void runFinally() {
        if (this.result == WorkStatus.FINISH) {
            this.queue.halt(this.work);
        } else {
            this.queue.workDone(this.work);
        }
    }

    @Override
    public String toString() {
        return "A:" + this.work.toString();
    }
}