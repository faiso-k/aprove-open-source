package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import aprove.verification.oldframework.Bytecode.Merger.*;

/**
 * Convenience class holding the result of a merge operation + the cost to
 * obtain the merged variable (relative to the merged varA and varB).
 */
public class AbstractNumberMergeResult {

    /**
     * Here we remember cost that resulted out of forcefully widening integers.
     */
    private CostType enforcedWideningCost;

    /**
     * Merged variable.
     */
    private AbstractNumber mergedVariable;

    /**
     * First variable that was used for the merge.
     */
    private AbstractNumber varA;

    /**
     * Cost of widening varA to mergedVariable;
     */
    private CostType varAtoMerged;

    /**
     * Second variable that was used for the merge.
     */
    private AbstractNumber varB;

    /**
     * Cost of widening varB to mergedVariable;
     */
    private CostType varBtoMerged;

    /**
     * Prepare a new class holding merge costs, setting the variables to be
     * merged.
     * @param a first {@link AbstractPrimitive} used in the merge
     * @param b second {@link AbstractPrimitive} used in the merge
     */
    public AbstractNumberMergeResult(final AbstractNumber a, final AbstractNumber b) {
        this.varA = a;
        this.varB = b;
    }

    /**
     * @return the cost that resulted out of forcefully widening some integer.
     * May be null!
     */
    public CostType getEnforcedWideningCost() {
        return this.enforcedWideningCost;
    }

    /**
     * @return the mergedVariable
     */
    public final AbstractNumber getMergedVariable() {
        return this.mergedVariable;
    }

    /**
     * @return the varA
     */
    public final AbstractNumber getVarA() {
        return this.varA;
    }

    /**
     * @return the varAtoMerged
     */
    public final CostType getVarAtoMerged() {
        return this.varAtoMerged;
    }

    /**
     * @return the varB
     */
    public final AbstractNumber getVarB() {
        return this.varB;
    }

    /**
     * @return the varBtoMerged
     */
    public final CostType getVarBtoMerged() {
        return this.varBtoMerged;
    }

    /**
     * Add the given cost to the cost of forcefully widening integers.
     * @param cost some cost to add.
     */
    public void setEnforcedWideningCost(final CostType cost) {
        this.enforcedWideningCost = cost;
    }

    /**
     * @param var the mergedVariable to set
     */
    public final void setMergedVariable(final AbstractNumber var) {
        this.mergedVariable = var;
    }

    /**
     * @param var the varA to set
     */
    public final void setVarA(final AbstractNumber var) {
        this.varA = var;
    }

    /**
     * @param c the varAtoMerged cost to set
     */
    public final void setVarAtoMerged(final CostType c) {
        this.varAtoMerged = c;
    }

    /**
     * @param var the varB to set
     */
    public final void setVarB(final AbstractNumber var) {
        this.varB = var;
    }

    /**
     * @param c the varBtoMerged cost to set
     */
    public final void setVarBtoMerged(final CostType c) {
        this.varBtoMerged = c;
    }

}
