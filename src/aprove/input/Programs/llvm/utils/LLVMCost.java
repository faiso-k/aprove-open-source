package aprove.input.Programs.llvm.utils;

import aprove.verification.oldframework.Bytecode.Merger.*;

/**
 * Enumeration of possible reasons to add costs when merging, including the
 * costs associated with each of these reasons.
 * @author Marc Brockschmidt, cryingshadow
 */
public enum LLVMCost {

    /**
     * The cost for widening an integer to a finite interval.
     */
    INTERVAL_FINITE(1.0),

    /**
     * The cost for widening an integer to an infinite interval.
     */
    INTERVAL_INFINITE(2.0),

    /**
     * The cost for shrinking an association offset.
     */
    LESS_ASSOCIATION_OFFSET(4.0),

    /**
     * The cost for an allocated area which only exists in one state.
     */
    LOST_ALLOCATED_AREA(20.0),

    /**
     * The cost for a reference which is only associated to an allocated memory area in one state.
     */
    LOST_ASSOCIATED_REF(10.0),

    /**
     * The cost for losing some heap entry.
     */
    LOST_HEAP_ENTRY(4.0),

    /**
     * The cost for losing some relation.
     */
    LOST_RELATION(6.0),

    /**
     * The cost for merging some reference more than once.
     */
    MULTIPLE_REFERENCE_MERGE(6.0),

    /**
     * No actual cost (needed for technical reasons).
     */
    NONE(0.0),

    /**
     * The cost for weakening a relation.
     */
    WEAKER_RELATION(4.0);

    /**
     * Converts some cost types (related to numbers) from the JBC enum to the LLVM enum.
     * @param costT Some JBC cost type.
     * @return A corresponding LLVM cost type.
     */
    public static LLVMCost convertJBCToLLVMCost(CostType costT) {
        switch (costT) {
        case NONE:
            return LLVMCost.NONE;
        case INTERVAL_FINITE:
            return LLVMCost.INTERVAL_FINITE;
        case INTERVAL_INFINITE:
            return LLVMCost.INTERVAL_INFINITE;
        default:
            throw new IllegalStateException("Cannot convert JBC cost type " + costT + " to LLVM cost");
        }
    }

    /**
     * The actual cost associated with a certain cost type.
     */
    private final double costValue;

    /**
     * @param costVal Actual cost associated with a certain cost type.
     */
    private LLVMCost(double costVal) {
        this.costValue = costVal;
    }

    /**
     * @return The measure for a certain cost as double.
     */
    public double getCostValue() {
        return this.costValue;
    }

}
