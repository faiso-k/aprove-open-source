package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Remove the node.
 * @author cotto
 */
public class NodeRemover extends MethodGraphWorker {

    /**
     * The node.
     */
    private final Node node;

    /**
     * Remove the node.
     * @param graph the graph
     * @param nodeParam the node
     */
    public NodeRemover(final MethodGraph graph, final Node nodeParam) {
        super(graph);
        this.node = nodeParam;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        final WriteLock lock = this.getMethodGraph().getGraphLock().writeLock();
        try {
            lock.lock();
            List<MethodGraphWorker> result = new ArrayList<>();
            this.getMethodGraph().removeNode(this.node, result);
            assert(result.isEmpty()) : "this is actually fine, it just never happened before";
            this.getMethodGraph().getTerminationGraph().addJobs(result);
        } finally {
            lock.unlock();
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
