package aprove.strategies.ExecutableStrategies;

import aprove.strategies.Abortions.*;

/**
 * When a submachine is created, it runs forever. A thrown AbortionException is not seen by the submachine. This class
 * checks for a thrown AbortionException and stops the handle.
 * @author cotto
 */
public final class HandleChecker {
    /**
     * Do not instantiate me.
     */
    private HandleChecker() {
    }

    /**
     * Wait for the handle to finish, then return. While waiting, check for a thrown AbortionException. If aborted, stop
     * the handle.
     * @param handle a handle for a (sub)machine
     * @param aborter an Abortion object used in the context outside of the (sub)machine of the handle
     */
    public static void check(final StrategyExecutionHandle handle, final Abortion aborter) {
        HandleChecker.check(handle, aborter, 100);
    }

    /**
     * Wait for the handle to finish, then return. While waiting, check for a thrown AbortionException. If
     * aborted, stop the handle.
     * @param handle a handle for a (sub)machine
     * @param aborter an Abortion object used in the context outside of the (sub)machine of the handle
     * @param msec check every msec msec
     */
    public static void check(final StrategyExecutionHandle handle, final Abortion aborter, final int msec) {
        while (true) {
            try {
                handle.waitForFinish(msec);
            } catch (final InterruptedException e) {
                throw new AbortionException("Interrupted");
            }
            if (handle.isFinished()) {
                return;
            } else {
                try {
                    aborter.checkAbortion();
                } catch (final AbortionException e) {
                    handle.stop("Aborted: " + e.getMessage());
                    throw e;
                }
            }
        }
    }
}
