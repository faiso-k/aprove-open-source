/**
 * @author marc
 */
package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

public class NEQRefinementEdge extends RefinementEdge {
    /**
     * One of the two references.
     */
    private final AbstractVariableReference refOne;

    /**
     * The other one.
     */
    private final AbstractVariableReference refTwo;

    public NEQRefinementEdge(
            final AbstractVariableReference ref1,
            final AbstractVariableReference ref2) {
        super(ref1 + " != " + ref2, Collections.<AbstractVariableReference, AbstractVariableReference>emptyMap());
        this.refOne = ref1;
        this.refTwo = ref2;
    }

    /**
     * @return the refOne
     */
    public AbstractVariableReference getRefOne() {
        return this.refOne;
    }

    /**
     * @return the refTwo
     */
    public AbstractVariableReference getRefTwo() {
        return this.refTwo;
    }

    public boolean hasRef(final AbstractVariableReference ref) {
        return this.refOne.equals(ref) || this.refTwo.equals(ref);
    }
}
