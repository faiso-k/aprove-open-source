package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

@SuppressWarnings("serial")
public class RealizationRefinementEdge extends RefinementEdge {

    private AbstractVariableReference refinedRef;
    private AbstractVariableReference replacement;

    public RealizationRefinementEdge(AbstractVariableReference refinedRef, AbstractVariableReference replacement) {
        super(refinedRef, replacement);
        this.refinedRef = refinedRef;
        this.replacement = replacement;
    }

    public AbstractVariableReference getRefinedRef() {
        return refinedRef;
    }

    public AbstractVariableReference getReplacement() {
        return replacement;
    }
}
