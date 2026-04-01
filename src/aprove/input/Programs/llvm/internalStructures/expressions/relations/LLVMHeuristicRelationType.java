package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Indicates which kind of relation is represented.
 * @author Janine Repke, cryingshadow
 */
public enum LLVMHeuristicRelationType {

    /**
     * Equal to relation.
     */
    EQ("="),

    /**
     * Less than or equal to relation.
     */
    LE("<="),

    /**
     * Less than relation.
     */
    LT("<"),

    /**
     * Unequal to relation.
     */
    NE("!=");

    /**
     * @param type Some IntegerRelationType.
     * @return The corresponding RelationType, if type is one of LE, LT, EQ, NE. Null otherwise.
     */
    public static LLVMHeuristicRelationType fromIntegerRelationType(IntegerRelationType type) {
        if (type == null) {
            return null;
        }
        switch (type) {
            case EQ:
                return LLVMHeuristicRelationType.EQ;
            case LE:
                return LLVMHeuristicRelationType.LE;
            case LT:
                return LLVMHeuristicRelationType.LT;
            case NE:
                return LLVMHeuristicRelationType.NE;
            case GE:
            case GT:
                return null;
            default:
                throw new IllegalStateException("Someone found a new way to relate integers");
        }
    }

    /**
     * String representation of the respective relation.
     */
    private String symbol;

    /**
     * @param sym String representation of the respective relation.
     */
    private LLVMHeuristicRelationType(String sym) {
        this.symbol = sym;
    }

    /**
     * @param other Some other RelationType
     * @return The strictest RelationType ret such that for all x and y the following holds: (x this y && x other y)
     *         <==> x ret y or null if no such relation exists.
     */
    public LLVMHeuristicRelationType intersect(LLVMHeuristicRelationType other) {
        return
            LLVMHeuristicRelationType.fromIntegerRelationType(
                this.toIntegerRelationType().intersect(other.toIntegerRelationType())
            );
    }

    /**
     * @return True if for all x and y the following holds: x this y <==> y this x
     */
    public boolean isSymmetrical() {
        return this.equals(EQ) || this.equals(NE);
    }

    /**
     * @param other Some other RelationType
     * @return The strictest RelationType ret such that for all x and y the following holds: (x this y || x other y)
     *         <==> x ret y or null if no such relation exists.
     */
    public LLVMHeuristicRelationType merge(LLVMHeuristicRelationType other) {
        return
            LLVMHeuristicRelationType.fromIntegerRelationType(
                this.toIntegerRelationType().merge(other.toIntegerRelationType())
            );
    }

    /**
     * @return The corresponding IntegerRelationType.
     */
    public IntegerRelationType toIntegerRelationType() {
        switch (this) {
            case EQ:
                return IntegerRelationType.EQ;
            case NE:
                return IntegerRelationType.NE;
            case LE:
                return IntegerRelationType.LE;
            case LT:
                return IntegerRelationType.LT;
            default:
                throw new IllegalStateException("Unknown relation code!");
        }
    }

    @Override
    public String toString() {
        return this.symbol;
    }

}
