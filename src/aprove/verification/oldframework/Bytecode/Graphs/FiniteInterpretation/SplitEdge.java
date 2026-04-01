package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import immutables.*;


/**
 * Marks edges where we have arbitrarily decided the truth value of a condition.
 * @author Marc Brockschmidt
 */
public class SplitEdge extends RefinementOrSplitEdge {
    /** The references that could not be refined to avoid the split. */
    private final ImmutableSet<AbstractVariableReference> splitRefs;

    /**
     * @param splitRs the references that could not be refined to avoid the
     *  split.
     */
    public SplitEdge(final Set<AbstractVariableReference> splitRs) {
        this.splitRefs = ImmutableCreator.create(splitRs);
    }

    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = -1406034530715648230L;

    @Override
    public String toString() {
        return "Split";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#ffde00\"";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getLabel() {
        return "";
    }

    public ImmutableSet<AbstractVariableReference> getSplitRefs() {
        return this.splitRefs;
    }
}
