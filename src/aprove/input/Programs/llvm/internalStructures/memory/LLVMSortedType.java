package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;
import java.util.List;

public enum LLVMSortedType {

    /**
     * All values are equal (= non-ascending and non-descending).
     */
    ALLEQUAL("="),

    /**
     * Ascending.
     */
    ASCENDING("<"),

    /**
     * Descending.
     */
    DESCENDING(">"),

    /**
     * Non-Ascending.
     */
    NONASCENDING("<="),

    /**
     * Non-Descending.
     */
    NONDESCENDING(">="),

    /**
     * Unsorted.
     */
    UNSORTED("?");

    /**
     * A short string representation.
     */
    private String string;

    /**
     * @param stringParam a short string representation
     */
    LLVMSortedType(final String stringParam) {
        this.string = stringParam;
    }
    
    public static LLVMSortedType get(BigInteger change) {
        if (change == null) {
            return LLVMSortedType.UNSORTED;
        } else if (change.compareTo(BigInteger.ZERO) > 0) {
            return LLVMSortedType.ASCENDING;
        } else if (change.compareTo(BigInteger.ZERO) < 0) {
            return LLVMSortedType.DESCENDING;
        } else {
            return LLVMSortedType.ALLEQUAL;
        }
    }
    
    public static LLVMSortedType get(List<BigInteger> values) {
        boolean allequal = true;
        boolean ascending = true;
        boolean descending = true;
        boolean nonascending = true;
        boolean nondescending = true;
        for (int i = 1; i < values.size(); i++) {
            BigInteger diff = values.get(i).subtract(values.get(i-1));
            if (diff.compareTo(BigInteger.ZERO) == 0) {
                ascending = false;
                descending = false;
            } else if (diff.compareTo(BigInteger.ZERO) < 0) {
                allequal = false;
                ascending = false;
                nondescending = false;
            } else if (diff.compareTo(BigInteger.ZERO) > 0) {
                allequal = false;
                descending = false;
                nonascending = false;
            }
        }
        if (allequal) return ALLEQUAL;
        if (ascending) return ASCENDING;
        if (descending) return DESCENDING;
        if (nonascending) return NONASCENDING;
        if (nondescending) return NONDESCENDING;
        return UNSORTED;
    }
    
    public static LLVMSortedType min(LLVMSortedType first, LLVMSortedType second) {
        switch (first) {
        case ALLEQUAL:
            if (second == ALLEQUAL) return ALLEQUAL;
            if (second == ASCENDING || second == NONDESCENDING) return NONDESCENDING;
            if (second == DESCENDING || second == NONASCENDING) return NONASCENDING;
            return UNSORTED;
        case ASCENDING:
            if (second == ALLEQUAL || second == NONDESCENDING) return NONDESCENDING;
            if (second == ASCENDING) return ASCENDING;
            return UNSORTED;
        case DESCENDING:
            if (second == ALLEQUAL || second == NONASCENDING) return NONASCENDING;
            if (second == DESCENDING) return DESCENDING;
            return UNSORTED;
        case NONASCENDING:
            if (second == ALLEQUAL || second == DESCENDING || second == NONASCENDING) return NONASCENDING;
            return UNSORTED;
        case NONDESCENDING:
            if (second == ALLEQUAL || second == ASCENDING || second == NONDESCENDING) return NONDESCENDING;
            return UNSORTED;
        default:
            return UNSORTED;
        }
    }

    /**
     * @return a short string representation
     */
    public String toString() {
        return this.string;
    }

}
