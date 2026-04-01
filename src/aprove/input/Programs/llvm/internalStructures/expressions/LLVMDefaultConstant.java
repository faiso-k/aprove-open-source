package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Just a wrapper class for a BigInteger.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMDefaultConstant extends PlainIntegerConstant implements LLVMConstant {

    /**
     * The constant -1.
     */
    static final LLVMDefaultConstant NEGONE = new LLVMDefaultConstant(IntegerUtils.NEGONE);

    /**
     * The constant 1.
     */
    static final LLVMDefaultConstant ONE = new LLVMDefaultConstant(BigInteger.ONE);

    /**
     * The constant 0.
     */
    static final LLVMDefaultConstant ZERO = new LLVMDefaultConstant(BigInteger.ZERO);

    /**
     * @param v The value.
     * @return A constant with the specified value.
     */
    static LLVMDefaultConstant create(BigInteger v) {
        if (BigInteger.ZERO.equals(v)) {
            return LLVMDefaultConstant.ZERO;
        } else if (BigInteger.ONE.equals(v)) {
            return LLVMDefaultConstant.ONE;
        } else if (IntegerUtils.NEGONE.equals(v)) {
            return LLVMDefaultConstant.NEGONE;
        }
        return new LLVMDefaultConstant(v);
    }

    /**
     * @param v The value.
     */
    LLVMDefaultConstant(BigInteger v) {
        super(v);
    }

    @Override
    public LLVMConstant evaluate(LLVMTermFactory factory) {
        return this;
    }

    @Override
    public LLVMConstant negate() {
        return LLVMDefaultConstant.create(this.getIntegerValue().negate());
    }

}
