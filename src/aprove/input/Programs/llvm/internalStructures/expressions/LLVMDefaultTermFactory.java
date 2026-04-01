package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;

import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Offers a default term factory for LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMDefaultTermFactory implements LLVMTermFactory {

    /**
     * The default factory.
     */
    public static final LLVMTermFactory LLVM_DEFAULT_TERM_FACTORY;

    /**
     * Minus one.
     */
    private static final LLVMConstant NEGONE;

    /**
     * One.
     */
    private static final LLVMConstant ONE;

    /**
     * Zero.
     */
    private static final LLVMConstant ZERO;

    static {
        LLVM_DEFAULT_TERM_FACTORY = new LLVMDefaultTermFactory();
        ZERO = LLVMDefaultConstant.create(BigInteger.ZERO);
        ONE = LLVMDefaultConstant.create(BigInteger.ONE);
        NEGONE = LLVMDefaultConstant.create(IntegerUtils.NEGONE);
    }

    /**
     * No instantiation from outside.
     */
    private LLVMDefaultTermFactory() {
        // do not instantiate me from outside
    }

    @Override
    public LLVMConstant negone() {
        return LLVMDefaultTermFactory.NEGONE;
    }

    @Override
    public LLVMConstant one() {
        return LLVMDefaultTermFactory.ONE;
    }

    @Override
    public LLVMConstant zero() {
        return LLVMDefaultTermFactory.ZERO;
    }

}
