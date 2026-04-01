package aprove.strategies.Util;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;

/**
 * MultiProcessor framework. To use this framework, implement the interface {@link MultiProcessor}.
 * The process() method can then instantiate and use this class.
 *
 * For an example implementation, see {@link aprove.verification.dpframework.TRSProblem.Processors.QTRSMultiRRRProcessor}.
 *
 * @author Karsten Behrmann
 */
public class MultiProcessorHelper<ProblemType extends BasicObligation, SubResultType> {
    private final MultiProcessor<ProblemType, SubResultType> processor;
    private final int arity;

    /* Those two values contain the time length until deadline at first,
     * until collect() is called. Then, they contain absolute time values.
     */
    private long deadline = Long.MAX_VALUE;
    private long min_deadline = 0;
    // this one always contains a length.
    private long gracetime = Long.MAX_VALUE;

    private List<SubResultType> results;
    private int runningProcessors;

    public MultiProcessorHelper(MultiProcessor<ProblemType, SubResultType> processor, int arity) {
        this.processor = processor;
        this.arity = arity;
        this.results = new ArrayList<SubResultType>(arity);
    }

    /**
     * Sets the maximum number of milliseconds (wall time) that we will wait
     * for any results.
     */
    public synchronized void setDeadline(long millis) {
        if (this.runningProcessors > 0) {
            throw new IllegalStateException("cannot setDeadline anymore once I'm running!");
        }
        this.deadline = millis;
    }

    /**
     * Sets the number of milliseconds we will wait for further results
     * after the first one has arrived.
     */
    public synchronized void setGracetime(long millis) {
        this.gracetime = millis;
    }

    /**
     * Sets the minimum time we will let processors run.
     * That is, if the first subtask is successful after 10 milliseconds,
     * gracetime is 100 milliseconds, and this is 200 milliseconds,
     * we terminate everything after 200 milliseconds, not 110.
     *
     * Has no effect if gracetime is not set.
     */
    public synchronized void setMinDeadline(long millis) {
        this.min_deadline = millis;
    }

    public Result process(ProblemType qtrs, Abortion aborter) throws AbortionException {
        if (this.deadline != Long.MAX_VALUE) {
            this.deadline = System.currentTimeMillis() + this.deadline;
        }
        this.min_deadline = System.currentTimeMillis() + this.min_deadline;

        Abortion subAborter = aborter.createChild();

        this.runningProcessors = this.arity;
        for(int i=0; i<this.arity; i++) {
            ResultRunner runner = new ResultRunner(i, qtrs, subAborter);
            ThreadingPolicy.DEFAULT.schedule(runner);
        }

        synchronized(this) {
            while(this.runningProcessors > 0) {
                long currentTime = System.currentTimeMillis();
                if (currentTime >= this.deadline) {
                    break;
                }
                try {
                    this.wait(this.deadline - currentTime);
                } catch (InterruptedException e) {
                    subAborter.abort("interrupted");
                    throw new AbortionException("interrupted");
                }
            }
        }

        subAborter.abort("Multi done");
        synchronized(this) {
            return this.processor.merge(qtrs, this.results, aborter);
        }
    }

    synchronized void receiveResult(SubResultType subResult) {
        if (subResult == null) {
            return;
        }
        this.results.add(subResult);
        if (this.results.size() == 1 && this.gracetime != Long.MAX_VALUE) {
            // First result, adjust deadline
            this.deadline = Math.max(this.min_deadline, System.currentTimeMillis() + this.gracetime);
            this.notifyAll(); // Wake up new thread so it notices the new deadline
        }
    }

    synchronized void runnerFinished() {
        this.runningProcessors -= 1;
        if (this.runningProcessors == 0) {
            this.notifyAll();
        }
    }

    private class ResultRunner extends PooledJob {
        private int i;
        private ProblemType qtrs;
        private final Abortion aborter;

        public ResultRunner(int i, ProblemType qtrs, Abortion aborter) {
            super(aborter);
            this.i = i;
            this.qtrs = qtrs;
            this.aborter = aborter;
        }

        @Override
        public void wrappedRun() throws AbortionException {
            SubResultType subResult = MultiProcessorHelper.this.processor.processSub(this.i, this.qtrs, this.aborter);
            MultiProcessorHelper.this.receiveResult(subResult);
        }

        @Override
        public void runFinally() {
            MultiProcessorHelper.this.runnerFinished();
        }

        @Override
        public String shortName() {
            return "MultiRunner " + this.i + " of " + MultiProcessorHelper.this.processor.getName();
        }
    }
}
