package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Creates a new method end when executed.
 * @author Fabian K&uuml;rten
 */
public class MethodEndCreator extends MethodGraphWorker {

    /**
     * The listener to call. The listener will take care of computing the
     * new state.
     */
    private final MethodEndListener l;

    /**
     * The end state.
     */
    private final State endState;

    /**
     * Create the worker.
     * @param terminationGraphWorker the main worker
     */
    public MethodEndCreator(final MethodGraph methodGraph, final MethodEndListener listener, final State endStateParam)
    {
        super(methodGraph);
        this.l = listener;
        this.endState = endStateParam;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        // If the graph got removed, we don't need to do this.
        final Node node;
        final ReadLock lock = this.getMethodGraph().getGraphLock().readLock();
        try {
            lock.lock();
            // If the state was removed, we don't need to to this either.
            node = this.getMethodGraph().getNode(this.endState);
            if (!this.getMethodGraph().containsNode(node)) {
                return WorkStatus.CONTINUE;
            }
        } finally {
            lock.unlock();
        }
        // Release the first lock to prevent deadlocks.
        final MethodGraph targetGraph = this.l.getMethodGraph();
        final Node predNode = this.l.getNode();
        // If the target graph got removed, we don't need to do this.

        final Collection<MethodGraphWorker> newTasks;

        try {
            // If the predecessor was removed, noop.
            if (!targetGraph.containsNode(predNode)) {
                return WorkStatus.CONTINUE;
            }
            // if this graph does not contain the end node anymore, noop
            if (!this.getMethodGraph().containsNode(node)) {
                return WorkStatus.CONTINUE;
            }
            newTasks = this.l.newMethodEnd(this.getMethodGraph(), this.endState);
        } catch (final AssertionError e) {
            if (Globals.DEBUG_MARC || Globals.DEBUG_COTTO) {
                this.l.getMethodGraph().getTerminationGraph().dumpImage(false);
            }
            throw e;
        }
        if (newTasks != null) {
            this.getMethodGraph().getTerminationGraph().addJobs(newTasks);
        }
        return WorkStatus.CONTINUE;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        return this == obj;
    }
}
