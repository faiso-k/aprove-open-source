package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * A worker that does a specific merge job using the PathMerger.
 * @author cotto
 */
public class MergeWorker implements Runnable {
    /**
     * The first state to merge with.
     */
    private final State stateOne;

    /**
     * The second state to merge with.
     */
    private final State stateTwo;

    /**
     * The maximal cost allowed for the merge.
     */
    private final Double maxCost;
    /**
     * A flag indicating if the conversion is finished.
     */
    private boolean isDone;

    /**
     * The result of the merge.
     */
    private JBCMergeResult mergeResult;

    /**
     * True iff this worker was started already.
     */
    private boolean wasStarted;

    public MergeWorker(final State stateOneParam, final State stateTwoParam, final Double maximalMergeCosts) {
        this.stateOne = stateOneParam;
        this.stateTwo = stateTwoParam;
        this.maxCost = maximalMergeCosts;
        this.isDone = false;
        this.wasStarted = false;
    }

    /**
     * Wait for this merge to finish.
     * @throws InterruptedException when we are interrupted
     */
    public synchronized void waitForResult() throws InterruptedException {
        while (!this.isDone) {
            this.wait();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public synchronized void run() {
        this.wasStarted = true;
        final JBCMerger merger = new PathMerger(this.stateOne, this.maxCost);
        if (merger.merge(this.stateTwo)) {
            this.mergeResult = merger.getResult();
        } else {
            this.mergeResult = null;
        }
        this.isDone = true;
        this.notifyAll();
    }

    /**
     * @return the merge result
     */
    public synchronized JBCMergeResult getMergeResult() {
        assert (this.isDone);
        return this.mergeResult;
    }

    /**
     * @return true iff this worker was started already
     */
    public boolean wasStarted() {
        return this.wasStarted;
    }
}
