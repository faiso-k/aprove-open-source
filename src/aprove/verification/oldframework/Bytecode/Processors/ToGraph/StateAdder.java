package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * Adds a {@link State} to a {@link MethodGraph} when executed.
 * @author Fabian K&uuml;rten
 */
public class StateAdder extends MethodGraphWorker {
    /**
     * The predecessor in the graph.
     */
    private final Node pred;
    /**
     * The state to add.
     */
    private final State newState;
    /**
     * The edge connecting them.
     */
    private final EdgeInformation edge;

    /**
     * Create the worker
     */
    public StateAdder(
        final MethodGraph methodGraph,
        final Node predParam,
        final State newStateParam,
        final EdgeInformation edgeParam)
    {
        super(methodGraph);
        this.pred = predParam;
        this.newState = newStateParam;
        this.edge = edgeParam;

    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected WorkStatus executeInternally(final Abortion aborter) throws AbortionException {
        try {
            Collection<MethodGraphWorker> newTasks = null;
            while (newTasks == null) {
                newTasks = this.getMethodGraph().addStateToGraph(this.pred, this.newState, this.edge);
                if (Globals.DEBUG_COTTO && newTasks == null) {
                    this.getMethodGraph().getTerminationGraph().dumpImage(false);
                    System.err.println("repeating task: " + this.pred + " " + this.newState + " " + this.edge);
                }
            }

            this.getMethodGraph().getTerminationGraph().addJobs(newTasks);
        } catch (final AssertionError e) {
            this.getMethodGraph().getTerminationGraph().dumpImage(false);
            throw e;
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
