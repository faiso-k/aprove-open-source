package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Worker class used to expand leaves in this method graph. Based on the
 * implementation, there are several special ways to expand (e.g. when a method
 * call happens).
 */
public abstract class StateNodeExpander extends MethodGraphWorker {
    /**
     * The (leaf) node that should be expanded:
     */
    private final Node nodeToExpand;

    private boolean checkGraph;
    private boolean dumpGraph;

    /**
     * Constructs a new worker expanding the node passed as argument.
     * @param node Some (leaf) node in the constructed method graph that should
     * be expanded.
     * @param graph the method graph containing the node
     */
    public StateNodeExpander(final MethodGraph graph, final Node node) {
        super(graph);
        this.nodeToExpand = node;
    }

    public void checkGraph() {
        this.checkGraph = true;
    }

    public void dumpGraph() {
        this.dumpGraph = true;
    }

    /**
     * Actually perform the scheduled expansion, processing the current leaf
     * node, resulting in new nodes and edges. Depending on the special
     * expansion mode provided to the task, more involved tasks will be done.
     * @return always WorkStatus.CONTINUE
     * @param aborter unused
     * @throws AbortionException if the aborter kicks in
     */
    @Override
    public WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        TerminationGraph termG = this.getMethodGraph().getTerminationGraph();
        if (checkGraph) {
            termG.check();
            checkGraph = false;
        }
        if (dumpGraph) {
            termG.dumpImage(false);
            dumpGraph = false;
        }
        if (termG.getJBCOptions().indicateProgress() && termG.getProcessedNodes().get() % 100 == 0) {
            System.err.print(".");
        }

        try {
            if (this.getMethodGraph().containsNode(this.nodeToExpand) && !this.nodeToExpand.hasInstanceSucc()) {
                this.executeInternally();
            }
        } catch (final AssertionError e) {
            this.getMethodGraph().getTerminationGraph().dumpImage(false);
            throw e;
        }
        return WorkStatus.CONTINUE;
    }

    /**
     * Do the actual work.
     * @throws AbortionException if the aborter kicks in
     */
    protected abstract void executeInternally() throws AbortionException;

    /**
     * @return the node that should be expanded
     */
    protected Node getNodeToExpand() {
        return this.nodeToExpand;
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
