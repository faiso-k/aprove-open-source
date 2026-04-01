package aprove.verification.dpframework;

/**
 * A bare interface for objects that need to hook into the abortion hierarchy
 * in order to get instant notifications of abortions and the chance to react
 * to time refreshing events.
 *
 * Note that this may call abort() from the time refresher thread, so you
 * should not do overly lengthy or expensive operations when called
 * through this interface
 * @author BearPerson
 *
 */
public interface AbortionChild {

    /**
     * Makes this Abortion and all its children update [cpu] time used.
     * Does nothing when we already are aborted.
     */
    public void refreshTime();

    /**
     * Aborts this Abortion and all its children
     */
    public void abort(String reason);

}