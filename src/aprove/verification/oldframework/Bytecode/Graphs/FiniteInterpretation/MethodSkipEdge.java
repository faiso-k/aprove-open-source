package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This is a standard evaluation that is added iff we skip a method. This means
 * this edge connects a method call to a method return.
 * @author Fabian K&uuml;rten
 */
public class MethodSkipEdge extends EdgeInformation implements StateDeletionListener {

    /**
     * Some UID.
     */
    private static final long serialVersionUID = -833973440775618681L;

    /**
     * The node that was used to skip.
     */
    private Node node;

    /**
     * The graph containing the node.
     */
    private MethodGraph graph;

    /**
     * A map renaming all unchanged (!) references in the calling state to the
     * corresponding references in the resulting state.
     */
    private Map<AbstractVariableReference, AbstractVariableReference> callingToResultUnchangedMap;
    private Map<AbstractVariableReference, Pair<AbstractVariableReference, AbstractVariableReference>> callToResultEndChangedMap;

    /**
     * A map renaming all references in the returning state to the corresponding
     * references in the resulting state.
     */
    private Map<AbstractVariableReference, AbstractVariableReference> returningToResultMap;

    /**
     * @param nodeParam the node that was used to skip
     * @param graphParam the graph containing the node
     * @param callingToResult @see {@link MethodSkipEdge#callingToResultMap}
     * @param returningToResult @see {@link MethodSkipEdge#returningToResultMap}
     */
    public MethodSkipEdge (
        final Node nodeParam,
        final MethodGraph graphParam,
        final Map<AbstractVariableReference, AbstractVariableReference> callingToResultUnchanged,
        final Map<AbstractVariableReference, Pair<AbstractVariableReference, AbstractVariableReference>> callToResultEndChanged,
        final Map<AbstractVariableReference, AbstractVariableReference> returningToResult)
    {
        assert (nodeParam != null);
        this.node = nodeParam;
        this.graph = graphParam;
        this.callingToResultUnchangedMap = callingToResultUnchanged;
        this.callToResultEndChangedMap = callToResultEndChanged;
        this.returningToResultMap = returningToResult;
        if (!this.node.getState().addDeletionListener(this)) {
            this.node = null;
            this.graph = null;
            this.callingToResultUnchangedMap = null;
            this.callToResultEndChangedMap = null;
            this.returningToResultMap = null;
        }
    }

    /**
     * @return the node that was used to skip
     */
    public Node getNode() {
        return this.node;
    }

    @Override
    public String toString() {
        return "<<method skip>>" + super.toString();
    }

    /**
     * @return the graph containing the node
     */
    public MethodGraph getGraph() {
        return this.graph;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#ff00ff\"";
    }

    /**
     * @return a map renaming all unchanged (!) references in the calling state
     * to the corresponding references in the resulting state.
     */
    public Map<AbstractVariableReference, AbstractVariableReference> getCallingToResultUnchangedMap() {
        return callingToResultUnchangedMap;
    }

    public Map<AbstractVariableReference, Pair<AbstractVariableReference, AbstractVariableReference>> getCallToResultEndChangedMap() {
        return callToResultEndChangedMap;
    }

    /**
     * @return a map renaming all references in the returning state to the
     * corresponding references in the resulting state.
     */
    public Map<AbstractVariableReference, AbstractVariableReference> getReturningToResultMap() {
        return this.returningToResultMap;
    }

    /**
     * @return true if the skipped method (path) is pure (i.e., has no side effects)
     */
    public boolean callIsPure() {
        if (this.node == null) {
            return false;
        }
        final State methodReturnState = this.node.getState();
        final InputReferences inputRefs = methodReturnState.getInputReferences();

        //Changed a static field: We are done.
        if (!inputRefs.getChangedSF().isEmpty()) {
            return false;
        }

        //Changed
        for (final InputReference inputRef : inputRefs) {
            if (inputRef.getChanged()) {
                return false;
            }
        }

        return true;
    }

    /**
     * @param varPrefix a String that is prepended to the generated variables' name.
     * @return a list of SMTLIB atoms corresponding to the equalities between refs before and after the call
     */
    public List<SMTLIBTheoryAtom> toSMTAtoms(final String varPrefix) {
        final List<SMTLIBTheoryAtom> varEqualities = new LinkedList<>();
        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> e : this.callingToResultUnchangedMap
            .entrySet())
        {
            final AbstractVariableReference oldRef = e.getKey();
            final AbstractVariableReference newRef = e.getValue();
            if (oldRef.pointsToAnyIntegerType() && newRef.pointsToAnyIntegerType()) {
                varEqualities.add(SMTLIBIntEquals.create(
                    oldRef.toSMTIntValue(varPrefix),
                    newRef.toSMTIntValue(varPrefix)));
            }
        }
        return varEqualities;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void notifyStateDeletion(final State s) {
        if (this.node != null && this.node.getState() == s) {
            /* This marks this edge as unneeded. For now we keep it as we might merge with children.
             * It will be removed in the Graph post-processing in MethodGraph.removeUselessReturns()
             */
            this.node = null;
            this.graph = null;
            this.callingToResultUnchangedMap = null;
            this.callToResultEndChangedMap = null;
            this.returningToResultMap = null;
        }
    }
}
