package aprove.verification.oldframework.Utility.Multithread;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Util.*;

/**
 * Framework for multithreaded work.
 *
 * Define a list of jobs. Every job must extend {@link AbortableRunnable}.
 * The jobs will be scheduled via the queue or directly, if you use the ThreadingPolicy HIGH.
 * If started via the queue (this is the default behaviour) there is no quarantee when your jobs will be started.
 * Also there is no guarantee in which order they will be executed.
 *
 * There are currently two methods to access this framework: execute() and executeStopOnFinish()
 *
 * The execute() method starts every job until one returns FINISH.
 * Use this if you need all (CONTINUE) results, regardless of errors.
 *
 * The executeUntilError() starts every job until one returns FINISH or one terminates with an uncaught exception.
 * Use this if an error in one job makes the other jobs useless to you.
 *
 * All methods return the job responsible for stopping if there was one,
 * or null if all jobs completed with CONTINUE.
 *
 * @author Andreas Kelle-Emden
 * @author Karsten Behrmann
 */
public class MultithreadedExecutor {

    /**
     * Execute a given set of tasks with the standard threading policy (set via the command line).
     * Ignore occurring errors.
     *
     * @param workItems list of tasks
     * @param aborter Abortion
     */
    public static <T extends AbortableRunnable> T execute(List<T> workItems, Abortion aborter) throws AbortionException {
        return MultithreadedExecutor.execute(workItems, aborter, ThreadingPolicy.DEFAULT);
    }

    /**
     * Execute a given set of tasks with the standard threading policy (set via the command line).
     * If any error occurs this method stops the execution of left tasks.
     *
     * @param workItems list of tasks
     * @param aborter Abortion
     */
    public static <T extends AbortableRunnable> T executeUntilError(List<T> workItems,
            Abortion aborter) throws AbortionException {
        return MultithreadedExecutor.executeUntilError(workItems, aborter, ThreadingPolicy.DEFAULT);
    }

    /**
     * Execute a given set of tasks with the given threading policy.
     * Ignore occurring errors.
     *
     * @param workItems list of tasks
     * @param aborter Abortion
     * @param policy threading policy
     */
    public static <T extends AbortableRunnable> T execute(List<T> workItems, Abortion aborter, ThreadingPolicy policy) throws AbortionException {
        return MultithreadedExecutor.execute(workItems, aborter, policy, WorkStatus.CONTINUE);
    }

    /**
     * Execute a given set of tasks with the given threading policy.
     * If any error occurs this method stops the execution of left tasks.
     *
     * @param workItems list of tasks
     * @param aborter Abortion
     * @param policy threading policy
     */
    public static <T extends AbortableRunnable> T executeUntilError(List<T> workItems,
            Abortion aborter, ThreadingPolicy policy) throws AbortionException {
        return MultithreadedExecutor.execute(workItems, aborter, policy, WorkStatus.FINISH);
    }

    private static <T extends AbortableRunnable> T execute(List<T> workItems,
            Abortion aborter, ThreadingPolicy policy, WorkStatus exceptionResult) throws AbortionException {
        QueueManager<T> queue = new QueueManager<T>(aborter, exceptionResult);
        queue.setThreadingPolicy(policy);

        for(T item: workItems) {
            try {
                queue.add(item);
            } catch (AbortionException alreadyStopped) {
                return queue.getHaltReason();
            }
        }

        try {
            queue.waitForAll();
            return queue.getHaltReason();
        } catch (InterruptedException e) {
            throw new RuntimeException("MultithreadedExecutor interrupted while waiting for results");
        }
    }
}
