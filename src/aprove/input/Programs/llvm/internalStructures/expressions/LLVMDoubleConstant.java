package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

/**
 * Just a wrapper class for a Float.
 * @author Jera Hensel
 * @version $Id$
 */
public class LLVMDoubleConstant extends LLVMHeuristicConstRef implements LLVMConstant {
    
    private double value;
    
    LLVMDoubleConstant(double v) {
        super(BigInteger.ZERO);
        this.value = v;
    }

    /**
     * @param v The value.
     * @return A constant with the specified value.
     */
    static LLVMDoubleConstant create(double v) {
        return new LLVMDoubleConstant(v);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMDoubleConstant)) {
            return false;
        }
        LLVMDoubleConstant other = (LLVMDoubleConstant)obj;
        return this.getDoubleValue() == other.getDoubleValue();
    }

    @Override
    public LLVMConstant evaluate(LLVMTermFactory factory) {
        return this;
    }

    public double getDoubleValue() {
        return this.value;
    }

    @Override
    public LLVMHeuristicConstRef negate() {
        return LLVMDoubleConstant.create(this.getDoubleValue() * -1);
    }

}
