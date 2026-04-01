package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

/**
 * Just a wrapper class for a Float.
 * @author Jera Hensel
 * @version $Id$
 */
public class LLVMFloatConstant extends LLVMHeuristicConstRef implements LLVMConstant {
    
    private float value;
    
    LLVMFloatConstant(float v) {
        super(BigInteger.ZERO);
        this.value = v;
    }

    /**
     * @param v The value.
     * @return A constant with the specified value.
     */
    static LLVMFloatConstant create(float v) {
        return new LLVMFloatConstant(v);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMFloatConstant)) {
            return false;
        }
        LLVMFloatConstant other = (LLVMFloatConstant)obj;
        return this.getFloatValue() == other.getFloatValue();
    }

    @Override
    public LLVMConstant evaluate(LLVMTermFactory factory) {
        return this;
    }

    public float getFloatValue() {
        return this.value;
    }

    @Override
    public LLVMHeuristicConstRef negate() {
        return LLVMFloatConstant.create(this.getFloatValue() * -1);
    }

}
