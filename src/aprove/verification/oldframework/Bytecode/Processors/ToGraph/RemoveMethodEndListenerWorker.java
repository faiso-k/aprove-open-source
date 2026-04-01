package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Remove a method end listener for some now deleted (call) node.
 * @author cotto
 */
public class RemoveMethodEndListenerWorker extends MethodGraphWorker {
    /**
     * The deleted call node.
     */
    private final Node listeningNode;

    /**
     * @param graph the graph (maybe) serving data to the deleted listening node
     * @param listeningNodeParam the deleted call node
     */
    public RemoveMethodEndListenerWorker(final MethodGraph graph, final Node listeningNodeParam) {
        super(graph);
        this.listeningNode = listeningNodeParam;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        this.getMethodGraph().removeMethodEndListener(this.listeningNode);
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
