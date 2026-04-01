package aprove.verification.oldframework.Utility.Multithread;

import aprove.strategies.Abortions.*;

/**
 * This is the basic interface for every job class.
 *
 * @author Karsten Behrmann
 */
public interface AbortableRunnable {
    /**
     * Do your work in this method.
     *
     * Return WorkStatus.CONTINUE if execution should continue normally,
     * or WorkStatus.FINISH if you know other workers need not run anymore.
     *
     * Thrown exceptions will be logged, and translate into CONTINUE or FINISH
     * depending on which method from MultithreadedExecutor was called.
     */
    public WorkStatus execute(Abortion aborter) throws AbortionException;
}