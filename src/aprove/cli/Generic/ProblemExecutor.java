package aprove.cli.Generic;

import java.io.*;

import aprove.*;
import aprove.strategies.Abortions.*;

/**
 * Base class for solving a given problem.
 *
 * Subclass this, implement solve and printResult,
 * and create instances of it in your CommandLineOptions subclass.
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
public abstract class ProblemExecutor implements Runnable, ClockListener {

    protected boolean done = false;
    protected final boolean verbose;
    protected final boolean trackTime;
    protected volatile long millisAtStart;
    protected volatile long millisAtFinish;
    private Thread myThread = null;

    protected final Abortion abort;

    public ProblemExecutor(final CommandLineOptions opts) {
        this.verbose = opts.isVerbose();
        this.trackTime = opts.getPrintTimeSpent();
        if (opts.hasTimeLimit()) {
            Clock clock = new Clock(opts.getTimeLimit(), this);
            this.abort = AbortionFactory.create(clock);
        } else {
            this.abort = AbortionFactory.create();
        }
    }

    public synchronized void abort(final String why) {
        this.abort.abort(why);
        this.notifyAll();
    }

    @Override
    public void ring(Clock source) {
        this.abort();
    }

    public void abort() {
        this.abort("Timeout");
    }

    public boolean isFinished() {
        if (Globals.useAssertions) {
            /* As this condition is only meaningful for a thread waiting for us,
             * we ensure they are synchronized on us. If not, their wait() or suchlike
             * that they are going to do on us will break.
             * See Wiki at Code_Conventions#Threading_Pitfalls
             */
            assert(Thread.holdsLock(this));
        }
        if (this.done) {
            return true;
        }
        return this.abort.isAborted();
    }

    public void waitForResult() {
        synchronized(this) {
            while( ! this.isFinished()) {
                try {
                    this.wait();
                } catch (final InterruptedException shutUp) {
                    this.abort();
                }
            }
        }
    }

    public void waitForResult(final long timeoutMillis) {
        final long deadline = this.millisAtStart + timeoutMillis;
        long timeRemaining = 1;
        synchronized(this) {
            while( !this.isFinished() && (timeRemaining = deadline - System.currentTimeMillis()) > 0) {
                try {
                    this.wait(timeRemaining);
                } catch (final InterruptedException shutUp) {
                    timeRemaining = -1;
                    break;
                }
            }
        }
        if (timeRemaining <= 0) {
            this.abort();
        }
    }

    public synchronized void start() {
        /* We have to do this ourselves because millisAtStart needs to be set synchronously,
         * as waitForResult(long) needs it.
         */
        this.millisAtStart = System.currentTimeMillis();

        this.myThread = new Thread(this, "Problem executor thread");
        this.myThread.start();
        TrackerFactory.customThread(this.abort, this.myThread);
    }

    @Override
    public void run() {
        try {
            this.solve();
        } catch (final AbortionException aborted) {
            // Just to be sure...
            this.abort(aborted.getMessage());
            return;
        }

        synchronized(this) {
            if (this.trackTime) {
                this.millisAtFinish = System.currentTimeMillis();
            }

            this.done = true;
            this.notifyAll();
        }
    }

    public abstract void printResult(PrintWriter out);
    public abstract void solve() throws AbortionException;

    public synchronized void join() throws InterruptedException {
        this.myThread.join();
    }

}