package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

/**
 * Marker class for constants which are not merged, but just taken as they are. This is needed for distinguishing
 * merged constants from unmerged ones if constants with the same value have at some position been merged and at
 * another position have just been taken as they are.
 * @author CryingShadow
 */
public class LLVMNonMergedConstRef extends LLVMHeuristicConstRef {

    /**
     * @param number The value of this constant.
     * @param type The type of this constant.
     */
    public LLVMNonMergedConstRef(final BigInteger number) {
        super(number);
    }

    /**
     * @return This constant as normal (unmarked) constant.
     */
    public LLVMHeuristicConstRef asNormal() {
        return new LLVMHeuristicConstRef(this.getIntegerValue());
    }

}
