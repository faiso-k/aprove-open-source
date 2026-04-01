package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;

/**
 * The additive change within a (complex) memory invariant. May be a number (for a linear rate),
 * + (for sorted in ascending order), - (for sorted in descending order), or null.
 * @author Jera Hensel
 *
 */
public class LLVMAdditiveChange {
    
    private final BigInteger linearRate;
    
    /**
     * +1 for ascending, -1 for descending, 0 for unsorted
     */
    private final LLVMSortedType sorted;
    
    public LLVMAdditiveChange(BigInteger rate, LLVMSortedType sorted) {
        this.linearRate = rate;
        this.sorted = sorted;
    }
    
    public LLVMAdditiveChange(BigInteger rate) {
        this.linearRate = rate;
        if (rate == null) {
            sorted = LLVMSortedType.UNSORTED;
        } else if (rate.compareTo(BigInteger.ZERO) > 0) {
            this.sorted = LLVMSortedType.ASCENDING;
        } else if (rate.compareTo(BigInteger.ZERO) < 0) {
            this.sorted = LLVMSortedType.DESCENDING;
        } else {
            this.sorted = LLVMSortedType.ALLEQUAL;
        }
    }
    
    public BigInteger getLinearRate() {
        return this.linearRate;
    }
    
    public LLVMSortedType getSortedType() {
        return this.sorted;
    }
    
    public boolean isAscending() {
        return this.sorted == LLVMSortedType.ASCENDING;
    }
    
    public boolean isDescending() {
        return this.sorted == LLVMSortedType.DESCENDING;
    }
    
    public boolean isLinear() {
        return this.linearRate != null;
    }
    
    public boolean isNonAscending() {
        return this.sorted == LLVMSortedType.NONASCENDING;
    }
    
    public boolean isNonDescending() {
        return this.sorted == LLVMSortedType.NONDESCENDING;
    }
    
    public boolean isSorted() {
        return this.sorted != LLVMSortedType.UNSORTED;
    }
    
    public boolean isUnsorted() {
        return this.sorted == LLVMSortedType.UNSORTED;
    }
    
    public String toString() {
        if (this.linearRate != null) {
            if (this.linearRate.compareTo(BigInteger.ZERO) >= 0) {
                return "+" + this.linearRate;
            } else {
                return this.linearRate.toString();
            }
        } else if (this.sorted != null) {
            return this.sorted.toString();
        } else {
            return "?";
        }
    }
}
