package aprove.strategies.Abortions;

/**
 * Implement this interface to receive active notification from
 * abortions as soon as they are fired.
 *
 * Usually you will want to call checkAbortion periodically instead.
 */
public abstract class AbortionListener {
    /**
     * Remember the abortion object so that we can deregister.
     */
    private Abortion abortion = null;

    /**
     * Called when a listened abortion gets fired. As abortions are one-shot,
     * this method will be called at most once by any single abortion.
     *
     * Note that this method is called by the thread that fired the abortion,
     * which may be any thread.
     *
     * Be careful about shared state in this thread, and return quickly.
     *
     * @param source - the abortion that fired. Never null.
     * @param reason - the reason given in the abort. Never null.
     */
    public abstract void abortionFired(Abortion source, String reason);

    /**
     * Remember the abortion object so that we can deregister.
     * @param abortion the abortion
     */
    public void registerWithAbortion(final Abortion abortion) {
        assert (this.abortion == null);
        this.abortion = abortion;
    }

    /**
     * Call this method as soon as it is uninterested to get aborted.
     */
    public void deregisterWithAbortion() {
        if (this.abortion != null) {
            this.abortion.removeListener(this);
        }
    }
}
