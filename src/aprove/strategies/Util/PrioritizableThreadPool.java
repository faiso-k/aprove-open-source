package aprove.strategies.Util;

import java.util.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

/* Does not (yet) implement ExecutorService,
 * since we're not actually using that interface anywhere,
 * so adding all those methods would just be overkill.
 */

/**
 * A custom ThreadPool implementation with thread limit and queue.
 *
 * Essentially, the pool is always in one of three states:
 * - below capacity. There are idle workers, and new jobs will be processed immediately.
 * - at capacity. All workers are in use, new jobs will be queued, high-priority jobs start new threads.
 * - above capacity. We will let some workers terminate before we continue queue processing.
 *
 * We switch from the second to the third state when a high-priority job comes in
 * while we are already at capacity, we switch back when enough workers are done
 * that the number of worker threads again matches our configured limit.
 */
public class PrioritizableThreadPool implements Thread.UncaughtExceptionHandler {
    private static AtomicInteger WORKERCOUNT = new AtomicInteger();

    /* Reason we're not using ThreadPoolExecutor:
     * We need high-priority tasks that are never queued,
     * instead start a new thread if we're above our regular thread count.
     *
     * ThreadPoolExecutor could do that with a custom Queue,
     * but it keeps those extra threads around while there is work to do,
     * while we want to return to regular thread count as soon as possible,
     * and terminate threads as soon as we can.
     *
     * Note that this means we cannot just start extra threads,
     * since they would not affect our worker count.
     * We actually need to start more workers,
     * then kill the first workers that finish while we are above target.
     */

    public static final PrioritizableThreadPool INSTANCE = new PrioritizableThreadPool();
    private static final Logger log = Logger.getLogger("aprove.strategies.Util.PrioritizableThreadPool");


    /**
     * Configures how many workers we keep for regular tasks.
     */
    private int targetWorkers;

    public synchronized void setTargetWorkers(final int value) {
        this.targetWorkers = value;
        this.startWorkersIfNeeded();
    }

    /*
     * Locking policy: All mutable fields protected by synchronized(this).
     *
     * Could be improved upon with BlockingQueue and AtomicReference/Integer
     * when someone proves this to be a performance bottleneck.
     * Personally, I consider that unlikely.
     */

    /** Holds all regular tasks */
    private final Queue<Runnable> queue = new LinkedList<Runnable>();

    /** Holds high-priority tasks while new threads initialize,
     * usually empty pretty quickly.
     */
    private final LinkedList<Runnable> priorityQueue = new LinkedList<>();

    /** Holds and counts our running workers */
    private final Set<Worker> workers = new LinkedHashSet<Worker>();

    private final Queue<Reservation> reservations = new LinkedList<Reservation>();

    /**
     * Deactivated workers that might be re-activated again (to avoid having
     * short-lived threads, which is a bad idea for debugging). Also see
     * useReusableFeature.
     */
    private final Queue<Worker> spareWorkers = new LinkedList<>();

    /**
     * Iff set, we add surplus workers to spareWorkers and re-activate them
     * later.
     */
    private boolean useReusableFeature = false;

    /** Counts how many workers are waiting for something to do */
    private int idleWorkers = 0;

    /** Counts sleeping workers, that have called release() but not returned from acquire() yet.*/
    private int sleepingWorkers = 0;
    private final int defaultNumOfWorkers;

    /**
     * Constructs a new thread pool with default resource policy:
     * Keep as many threads as we have CPUs.
     */
    private PrioritizableThreadPool() {
        this(Math.max(Runtime.getRuntime().availableProcessors() * 2, 4));
    }

    /**
     * Constructs a new thread pool that keeps targetWorkers worker threads alive.
     *
     * If you need to construct dynamic instances of this class, fix it and
     * add a shutdown() method, because otherwise we are never garbage collected,
     * kept alive by our never-dying Worker threads.
     */
    private PrioritizableThreadPool(final int targetWorkers) {
        this.targetWorkers = targetWorkers;
        this.defaultNumOfWorkers = targetWorkers;
        this.startWorkersIfNeeded();
    }

    /**
     * Submit a task for execution.
     *
     * Actual execution of the task may be deferred
     * until a thread becomes available,
     * but a FIFO queue policy is maintained.
     */
    public synchronized void execute(final Runnable task) {
        this.queue.add(task);
        //System.err.println("execute()");
        //System.err.println (System.currentTimeMillis() + " Q status: " + this);
        this.notify();
    }

    /**
     * Execute the given tasks right now. This call returns after all tasks have
     * been started. If each task finishes after finite time, it is guaranteed
     * that this method terminates.<br>
     * In addition as many additional workers as given in blockedWorkers are
     * made available (i.e. by starting them, if they there are no surplus
     * workers, yet). The idea here is that some workers are blocked by a lock
     * (that will not be released until this method is done), so we make use of
     * the available CPU time for these workers while they wait. These
     * additional workers will be removed at the end of this method.
     * @param tasks the tasks to execute
     * @param blockedWorkers this many additional workers might be started
     * @throws InterruptedException if we are interrupted while waiting for
     * being respawned
     */
    public void executeNowAndWait(final Collection<? extends Runnable> tasks, final int blockedWorkers)
            throws InterruptedException {
        final Reservation reservation;
        final int additionalWorkers;
        synchronized (this) {
            // figure out if we want to start new workers (to run while other workers are waiting for some lock)
            final int wantedAdditionalWorkers = Math.min(blockedWorkers, tasks.size());
            final int wantedWorkers = this.defaultNumOfWorkers + wantedAdditionalWorkers;

            additionalWorkers = wantedWorkers - this.targetWorkers;
            if (additionalWorkers > 0) {
                this.targetWorkers += additionalWorkers;
            }
            final LinkedList<Runnable> list = new LinkedList<>(tasks);
            final ListIterator<Runnable> it = list.listIterator(list.size());
            while (it.hasPrevious()) {
                final Runnable task = it.previous();
                this.priorityQueue.addFirst(task);
            }
            this.release();
            reservation = new Reservation();
            this.reservations.add(reservation);
            this.notify();
        }

        reservation.waitFor();
        synchronized (this) {
            if (additionalWorkers > 0) {
                this.targetWorkers -= additionalWorkers;
            }
        }
    }

    /**
     * Submit a task for immediate execution.
     *
     * Execution is now, even if we need to start another thread to do so.
     * In that case, processing of the regular queue is halted
     * until enough tasks finish to get us back on the regular number of threads.
     */
    public synchronized void executeNow(final Runnable task) {
        this.priorityQueue.add(task);
        if (this.idleWorkers < this.priorityQueue.size()) {
            // Forcibly create another thread to pick up the new work item
            this.startWorker();
        }
        //System.err.println("executeNow()");
        //System.err.println ("Q status: " + this);
        this.notify();
    }

    /**
     * Release a spot in the threadpool.
     *
     * After calling this method, you should not use significant CPU time
     * until you call acquire() again to get your spot back
     *
     * Useful if you submit other work to the threadpool and need to sleep
     * until that work is done, since otherwise you might deadlock, occupying
     * the very spot your pool threads need to do your work.
     */
    public synchronized void release() {
        this.sleepingWorkers++;
        this.startWorkersIfNeeded();
    }

    /**
     * Get your spot in the threadpool back.
     *
     * Always call this method after you called release()
     */
    public void acquire() throws InterruptedException {
        final Reservation reservation = new Reservation();
        synchronized(this) {
            this.reservations.add(reservation);
            this.notify();
        }

        reservation.waitFor();
    }

    private class Reservation {
        private boolean finished;

        public synchronized void finish() {
            this.finished = true;
            this.notify();
        }

        public synchronized void waitFor() throws InterruptedException {
            while(! this.finished) {
                this.wait();
            }
        }
    }

    private class Worker implements Runnable {
        private final int id;
        /**
         * Iff true, we may re-activate this worker after it was done.
         */
        private boolean reusable = true;

        private boolean goToSleep = true;

        public Worker() {
            this.id = PrioritizableThreadPool.WORKERCOUNT.incrementAndGet();
        }

        @Override
        public String toString() {
            return this.id + "";
        }

        @Override
        public void run() {
            while (this.reusable) {
                if (!PrioritizableThreadPool.this.useReusableFeature) {
                    this.reusable = false;
                }
                try {
                    while (true) {
                        final Runnable job = PrioritizableThreadPool.this.fetchJob(this);
                        if (job == null) {
                            break;
                        } else {
                            assert (PrioritizableThreadPool.this.workers.contains(this));
                            job.run();
                        }
                    }
                } catch (final Throwable t) {
                    this.reusable = false;
                    throw (t);
                } finally {
                    if (!PrioritizableThreadPool.this.workerGone(this)) {
                        // just die
                        this.reusable = false;
                    }
                }
                if (this.reusable) {
                    try {
                        synchronized (this) {
                            if (this.goToSleep) {
                                this.wait();
                            }
                            this.goToSleep = true;
                        }
                    } catch (final InterruptedException e) {
                        this.reusable = false;
                        PrioritizableThreadPool.this.workerGone(this);
                    }
                }
            }
        }
    }

    /**
     * Fetches something for a worker to do, blocking if necessary.
     * @return a job, or null if the worker should terminate.
     */
    private synchronized Runnable fetchJob(final Worker worker) {
        while(true) {
            Runnable task;

            // Do we have a high-priority task?
            task = this.priorityQueue.poll();
            if (task != null) {
                return task;
            }

            // If we have threads waiting in acquire(), wake one up and terminate ourself
            final Reservation reservation = this.reservations.poll();
            if (reservation != null) {
                this.sleepingWorkers--;
                reservation.finish();
                return null;
            }

            // Are we a surplus worker?
            if (this.workers.size() > this.targetWorkers + this.sleepingWorkers) {
                // Decrement workers now, to avoid a race condition
                // where some workers try to exit simultaneously
                this.workers.remove(worker);

                /*
                 * This worker dies, but maybe the next worker should survive and actually do some work that is
                 * available.
                 */
                this.notify();
                return null;
            }

            // Do we have regular work to do?
            task = this.queue.poll();
            if (task != null) {
                //System.err.println ("Q status: " + this);
                return task;
            }

            // Oh well, wait until there's something to do.
            this.idleWorkers++;
            try {
                this.wait();
            } catch (final InterruptedException e) {
                this.idleWorkers--;
                return null;
            }
            this.idleWorkers--;
        }
    }

    /**
     * Called when a worker exits, and does internal bookkeeping.
     */
    private synchronized boolean workerGone(final Worker worker) {
        boolean addedSpare = false;
        this.workers.remove(worker);
        if (worker.reusable && this.spareWorkers.size() < this.defaultNumOfWorkers * 4) {
            this.spareWorkers.offer(worker);
            addedSpare = true;
        }
        // It is possible we lost a worker due to an exception.
        // In that case, start another one.
        this.startWorkersIfNeeded();
        return addedSpare;
    }

    /**
     * Call to ensure we have targetWorkers threads running.
     *
     * Must hold lock when calling this method!
     */
    private void startWorkersIfNeeded() {
        while(this.workers.size() < this.targetWorkers + this.sleepingWorkers) {
            this.startWorker();
        }
    }

    /**
     * Counter for threads.
     */
    private int id = 0;

    /**
     * Starts one worker thread. Must hold lock when calling this method!
     */
    private void startWorker() {
        Worker worker = this.spareWorkers.poll();
        if (worker != null) {
            this.workers.add(worker);
            synchronized (worker) {
                worker.goToSleep = false;
                worker.notify();
            }
            return;
        }
        worker = new Worker();
        this.workers.add(worker);
        final Thread workerThread = new Thread(worker);
        workerThread.setName("ThreadPoolThread" + this.id);
        this.id++;
        workerThread.setDaemon(true);
        workerThread.setUncaughtExceptionHandler(this);
        workerThread.start();
        assert (this.spareWorkers.isEmpty());
    }

    @Override
    public void uncaughtException(final Thread t, final Throwable e) {
        if (!(e instanceof ThreadDeath)) {
            PrioritizableThreadPool.log.log(Level.WARNING, "Threadpool thread died by not catching an exception", e);
        }
    }

    @Override
    public synchronized String toString() {
        return "PrioThreadPool(" +
                this.workers.size() + "/" + this.targetWorkers + " workers, " +
                this.idleWorkers + " idle, " + this.sleepingWorkers + " asleep, " +
                (this.queue.size()+this.priorityQueue.size()) + " jobs pending)";
    }

    /**
     * @return the number of target workers
     */
    public int getTargetWorkers() {
        return this.targetWorkers;
    }

    /**
     *
     */
    public static void enableReusableFeature() {
        PrioritizableThreadPool.INSTANCE.useReusableFeature = true;
    }
}
