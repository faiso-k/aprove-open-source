package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.Collections;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This edge is used when refining a possible equality.
 * @author cotto
 */
public class EQRefinementEdge extends RefinementEdge {
    /**
     * Some UID.
     */
    private static final long serialVersionUID = 6279896005086698930L;

    /**
     * For equality refinements, this is the replacement ref.
     */
    private final AbstractVariableReference replacementRef;

    /**
     * For equality refinements, this is the replaced ref.
     */
    private final AbstractVariableReference replacedRef;

    /**
     * Create an edge used to connect a state with a child created through
     * refinement.
     * @param l Label for this edge (can be used to indicate the performed
     * refinement)
     * @param replacementRefParam if this is an equality refinement, the
     * replacement reference
     * @param replacedRefParam if this is an equality refinement, the replaced
     * reference
     */
    public EQRefinementEdge(final String l,
            final AbstractVariableReference replacementRefParam,
            final AbstractVariableReference replacedRefParam,
            final boolean doNotMergeLoop) {
        super(l, Collections.singletonMap(replacedRefParam, replacementRefParam), doNotMergeLoop);
        this.replacementRef = replacementRefParam;
        this.replacedRef = replacedRefParam;
    }

    /**
     * @return the replacementRef (for equality refinements), null otherwise
     */
    public AbstractVariableReference getReplacementRef() {
        return this.replacementRef;
    }

    /**
     * @return the replacedRef (for equality refinements), null otherwise
     */
    public AbstractVariableReference getReplacedRef() {
        return this.replacedRef;
    }
}
