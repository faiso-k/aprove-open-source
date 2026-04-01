package aprove.verification.oldframework.Bytecode.Processors.ToGraph.CallExpander;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

public class DuplicateNRIRs extends StateNodeExpander {
    /**
     * @param node Some (leaf) node in the constructed method graph that should be expanded.
     * @param graph the method graph containing the node
     */
    public DuplicateNRIRs(final MethodGraph graph, final Node node) {
        super(graph, node);
    }

    /**
     * @throws AbortionException when the aborter kicks in
     */
    @Override
    protected void executeInternally() throws AbortionException {
        final State abstractedState = this.getNodeToExpand().getState();
        final State res = DuplicateNRIRs.duplicate(abstractedState);
        if (res == null) {
            final MethodGraphWorker standardTask =
                new ConnectToMethodGraph(this.getMethodGraph(), this.getNodeToExpand());
            this.getMethodGraph().getTerminationGraph().addJob(standardTask);
            return;
        }
        Collection<MethodGraphWorker> result = null;
        while (result == null) {
            result =
                this.getMethodGraph().addStateToGraph(
                    this.getNodeToExpand(),
                    res,
                    new InstanceEdgeTryToConnect("duplicated NRIRs"));
        }
        assert (result.size() <= 1);
        this.getMethodGraph().getTerminationGraph().addJobs(result);
    }

    /**
     * If there is a NRIR for reference x and reference x can be put onto the operand stack (for example, because it is
     * reachable from some argument), we instead use reference y for the NRIR and add x =?= y.
     * @param state the state to work on
     * @return null if nothing needs to be done, or a state where the NRIRs are separated from "reachable" references
     */
    public static State duplicate(final State state) {
        final HeapPositions heapPos = new HeapPositions(state);
        final Collection<NonRootInputReference> todo = new LinkedHashSet<>();
        for (final NonRootInputReference nrir : state.getInputReferences().getNonRootInputReferences()) {
            final AbstractVariableReference ref = nrir.getReference();
            for (final StatePosition pos : heapPos.getPositionsForRef(ref)) {
                final RootPosition rootPos = pos.getRootPosition();
                if (!(rootPos instanceof NonRootIRPosition)) {
                    todo.add(nrir);
                    break;
                }
            }
        }
        if (todo.isEmpty()) {
            return null;
        }

        final State clone = state.clone();
        final HeapAnnotations ha = clone.getHeapAnnotations();

        for (final NonRootInputReference nrir : todo) {
            final AbstractVariableReference ref = nrir.getReference();
            /*
             * Instead of using a NRIR with a reference available on the state (so it might be put onto the operand
             * stack), add a new reference to the state and connect it to the original ref. Then create a NRIR for the
             * new reference. This way we never have NRIRs on the operand stack.
             */
            AbstractVariableReference newRef;
            if (ha.isMaybeExisting(ref)) {
                newRef = AbstractVariableReference.create(ref);
            } else {
                newRef = clone.createReferenceAndAdd(new AbstractInstance(), ref.getPrimitiveType());
            }

            ha.mergeAnnotationsForNRIRMerge(clone, ref, newRef);
            if (ha.isMaybeExisting(newRef)) {
                clone.removeAbstractVariable(newRef);
            }

            ha.getEqualityGraph().addPossibleEquality(clone, ref, newRef);

            final NonRootInputReference newNRIR = nrir.clone();
            newNRIR.replaceReference(newRef);

            clone.getInputReferences().removeNRIR(nrir);
            clone.getInputReferences().add(newNRIR);
        }

        return clone;
    }
}
