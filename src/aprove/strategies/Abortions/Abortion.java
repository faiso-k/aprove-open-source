package aprove.strategies.Abortions;

import java.util.*;

/**
 * This class helps us cleanly terminate calculations that should be stopped.
 *
 * An abortion starts out not aborted, and at some point gets
 * <em>aborted</em>.
 *
 * This is a one-shot phenomenon: Once aborted, an abortion stays
 * in that state until garbage collection.
 *
 * Abortions are heavily used by multiple threads.
 * Unless stated otherwise, all public methods of this class
 * may be invoked by any thread, in any order.
 *
 * An Abortion is normally provided to processors,
 * and createChild() here should be sufficient to create any
 * further Abortions they need.
 *
 * If you are OUTSIDE the regular framework (inside a test case,
 * or writing a bare-bone main) and need a brand-new Abortion
 * instance, use one of the static methods in the AbortionFactory
 * class.
 */
public class Abortion extends AbortionListener {
    private final List<Clock> clocks;
    private volatile String aborted = null;
    private final Collection<AbortionListener> listeners = new LinkedHashSet<AbortionListener>();

    /**
     * Creates a new Abortion with the given clocks.
     *
     * That list MUST be immutable!
     *
     * (All methods in AbortionFactory ensure that it is).
     */
    Abortion(final List<Clock> clocks) {
        this.clocks = clocks;
    }

    /**
     * Queries if this abortion is aborted yet.
     *
     * @return null if we are not aborted, the reason if we are.
     */
    public synchronized String getAbortionReason() {
        return this.aborted;
    }

    /**
     * Throws AbortionException if we are aborted, does nothing otherwise.
     *
     * This method should be called periodically by processors,
     * the thrown exception can safely propagate to their caller.
     *
     * @throws AbortionException iff we are aborted when this method is called.
     */
    public void checkAbortion() throws AbortionException {
        // Get the reason thread-safely
        final String reason = this.getAbortionReason();

        if (reason != null) {
            throw new AbortionException(reason);
        }
    }

    /**
     * Queries if this abortion is aborted yet.
     */
    public boolean isAborted() {
        return this.getAbortionReason() != null;
    }

    /**
     * Creates a new child abortion.
     *
     * Semantics are the following:
     * When the parent becomes aborted, the child automatically
     * also aborts. However, the child can be aborted earlier
     * without affecting the abortion status of the parent.
     *
     * This method may be useful to implement sub-calculations
     * that are part of the overall calculation, but sometimes
     * need to be aborted independently (i.e. when solving a
     * problem via different means in different threads)
     *
     * @return a new child abortion. Never null.
     * @throws AbortionException if we were already aborted when this method was called
     */
    public Abortion createChild() throws AbortionException {
        final Abortion result = new Abortion(this.clocks);
        this.addListener(result); // Throws iff we are aborted
        return result;
    }

    /**
     * @see Abortion#createChild()
     * @param milliSec milliseconds
     * @return a new child abortion. Semantics are the following: When the parent becomes aborted, the child
     * automatically also aborts. However, the child can be aborted earlier without affecting the abortion status of the
     * parent. The returned child abortion aborts after milliSec milliseconds, but only if (IMPORTANT!) it is registered
     * with a tracker (otherwise the clock of the new timeout created here is never updated). However, SMTEngine.solve()
     * correctly registers so that the time spent in Yices/Z3/... is counted (but not the time needed inside the Java
     * classes, i.e. preprocessing and postprocessing).
     * @throws AbortionException if we were already aborted when this method was called
     */
    public Abortion createChild(final int milliSec) throws AbortionException {
        final Clock clock = new Clock(milliSec, null);

        final List<Clock> newList = new LinkedList<>(this.clocks);
        newList.add(clock);
        final Abortion child = new Abortion(newList);
        clock.setListener(new ClockListener() {
            @Override
            public void ring(final Clock source) {
                child.abort("time's up");
            }
        });
        // Throws iff we are aborted
        this.addListener(child);
        return child;
    }

    /**
     * Fires this abortion.
     *
     * If we are already aborted, calling this method has no effect.
     * Otherwise, we go into aborted state:
     * All abortion listeners are fired (from this thread),
     * any child abortions are also aborted, and any subsequent
     * calls to checkAbortion() will throw AbortionException.
     *
     * @param reason - the reason for the abortion. Must not be null.
     * @throws NullPointerException if reason was null
     */
    public void abort(final String reason) {
        if (reason == null) {
            throw new NullPointerException("reason");
        }

        synchronized (this) {
            if (this.aborted != null) {
                return;
            }
            this.aborted = reason;
        }

        /* Deadlock avoidance: drop lock before we notify listeners.
         * The collection will not be modified after this point,
         * see addListener().
         */
        for (final AbortionListener listener : this.listeners) {
            listener.abortionFired(this, reason);
        }

        this.listeners.clear();
    }

    /**
     * Adds a listener to this abortion.
     *
     * Listeners are notified when this abortion goes into aborted state.
     * If we are already aborted when this method is called, an AbortionException
     * is thrown instead, and the listener not notified.
     */
    public void addListener(final AbortionListener listener) throws AbortionException {
        synchronized (this) {
            if (this.aborted != null) {
                throw new AbortionException(this.aborted);
            }
            this.listeners.add(listener);
            listener.registerWithAbortion(this);
        }
    }

    /**
     * Adds a listener to this abortion.
     *
     * Equivalent to addListener, except that if this abortion is already aborted,
     * the listener is fired in the calling thread,
     * and no abortion thrown to calling code.
     */
    public void addListenerOrFire(final AbortionListener listener) {
        try {
            this.addListener(listener);
        } catch (final AbortionException e) {
            listener.abortionFired(this, e.getMessage());
        }
    }

    // Implementation note: there intentionally is no removeListener().
    // It is currently never needed, and it will be difficult to ensure
    // sane timing guarantees (ensuring a listener will not be fired
    // after removeListener returns.)

    /**
     * Notifies Clocks that the computation tracked by this Abortion
     * has just consumed some milliseconds of CPU time.
     *
     * Can be called after this abortion has fired, and will still
     * take effect.
     *
     * Generally only called by TimeTracker implementations.
     */
    public void increaseTime(final long millis) {
        // Note: RuntimeInformation.getClocks() contract guarantees
        // that we need not synchronize here.
        for (final Clock clock : this.clocks) {
            clock.increaseTime(millis);
        }
    }

    /**
     * Equivalent to {@link aprove.strategies.ExecutableStrategies.RuntimeInformation#getClocks()},
     * for the RuntimeInformation associated with this Abortion.
     *
     * Added for the benefit of RuntimeInformation,
     * you will not normally need this.
     */
    public List<Clock> getClocks() {
        return this.clocks;
    }

    /*
     * Implementation note: strictly speaking, the above two methods
     * do not belong here. However, it seems convenient (right now)
     * to give Processors a link to Clocks in the abortion, as they
     * carry that around all the time anyway.
     *
     * They need this whenever they start a new TimeTracker,
     * or a new Machine.
     */

    /**
     * Implement AbortionListener, only used to link child abortions:
     * Fires this abortion, unless it was already fired.
     */
    @Override
    public void abortionFired(final Abortion source, final String reason) {
        this.abort(reason);
    }

    /**
     * Removes a listener from this abortion.
     *
     * @param listener the listener
     */
    public void removeListener(final AbortionListener listener) {
        synchronized (this) {
            if (this.aborted == null) {
                this.listeners.remove(listener);
            }
        }
    }
}
