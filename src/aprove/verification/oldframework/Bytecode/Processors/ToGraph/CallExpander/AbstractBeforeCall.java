package aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 */
public class AbstractBeforeCall extends StateNodeExpander {
    /**
     * @param node Some (leaf) node in the constructed method graph that should
     * be expanded.
     * @param graph the method graph containing the node
     */
    public AbstractBeforeCall(final MethodGraph graph, final Node node) {
        super(graph, node);
    }

    /**
     * @throws AbortionException when the aborter kicks in
     */
    @Override
    protected void executeInternally() throws AbortionException {
        final State reducedState = this.getNodeToExpand().getState();
        final State abstractedState = AbstractBeforeCall.abstractForCall(reducedState);
        if (abstractedState == null) {
            final MethodGraphWorker task = new DuplicateNRIRs(this.getMethodGraph(), this.getNodeToExpand());
            this.getMethodGraph().getTerminationGraph().addJob(task);
            return;
        }
        Collection<MethodGraphWorker> result = null;
        while (result == null) {
            result =
                this.getMethodGraph().addStateToGraph(
                    this.getNodeToExpand(),
                    abstractedState,
                    new InstanceEdgeDuplicateNRIRs("abstracting before call"));
        }
        assert (result.size() <= 1);
        this.getMethodGraph().getTerminationGraph().addJobs(result);
    }

    /**
     * Create a more abstract version of the given state by replacing realized
     * instances referenced by some non-root input reference by abstract
     * instances.
     * @param state the state to work with
     * @return the abstracted state or null if nothing was done
     */
    public static State abstractForCall(final State state) {
        /*
         * TODO when disabling this, also take care that annotations/fields are
         * considered when copying NRIRs from one graph to another. Otherwise,
         * after merging, we still have some abstraction.
         * See ConnectToMethodGraph.copyToAbstractedState()
         */
        final Collection<AbstractVariableReference> refsToAbstractAway = new LinkedList<>();

        // find the non-root input references we want to abstract
        for (final InputReference ir : state.getInputReferences().getNonRootInputReferences()) {
            final AbstractVariableReference ref = ir.getReference();
            if (!ref.pointsToReferenceType()) {
                continue;
            }
            assert (!ref.isNULLRef());
            if (state.getHeapAnnotations().isMaybeExisting(ref)) {
                continue;
            }
            final AbstractVariable var = state.getAbstractVariable(ref);
            if (var instanceof AbstractInstance) {
                continue;
            }
            if (var instanceof ConcreteInstance) {
                final ConcreteInstance ai = (ConcreteInstance) var;
                if (ai.isOnlyRealizedUpToJLO()) {
                    continue;
                }
            }

            refsToAbstractAway.add(ref);
        }

        return state.replaceConcreteInstancesByAbstractedInstance(refsToAbstractAway, true);
    }
}
