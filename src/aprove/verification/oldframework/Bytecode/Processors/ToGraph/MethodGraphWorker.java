package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Worker class used to expand leaves in this method graph:
 */
public abstract class MethodGraphWorker implements AbortableRunnable {
    /**
     * The MethodGraph containing the node.
     */
    private final MethodGraph methodGraph;

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.methodGraph == null) ? 0 : this.methodGraph.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final MethodGraphWorker other = (MethodGraphWorker) obj;
        if (this.methodGraph == null) {
            if (other.methodGraph != null) {
                return false;
            }
        } else if (!this.methodGraph.equals(other.methodGraph)) {
            return false;
        }
        return true;
    }

    /**
     * @param graph the method graph containing the node
     */
    public MethodGraphWorker(final MethodGraph graph) {
        this.methodGraph = graph;
        graph.newWorker();
    }

    /**
     * @return the method graph that is part of the task (must exist for the
     * task to make sense)
     */
    public MethodGraph getMethodGraph() {
        return this.methodGraph;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public WorkStatus execute(final Abortion aborter) throws AbortionException {
        this.methodGraph.getTerminationGraph().getReadLock().lock();
        try {
            final WorkStatus res = this.executeInternally(aborter);
            if (res != WorkStatus.FINISH) {
                this.methodGraph.workerExecution();
            }
            return res;

        } finally {
            this.methodGraph.getTerminationGraph().getReadLock().unlock();
        }
    }

    /**
     * Do the actual execute() work.
     * @return FINISH when we're done, CONTINUE otherwise
     * @param aborter
     */
    protected abstract WorkStatus executeInternally(Abortion aborter) throws AbortionException;

    @Override
    public String toString() {
        return "MGW(" + this.getMethodGraph() + ", " + this.methodGraph.getTerminationGraph().hashCode() + ")";
    }
}
