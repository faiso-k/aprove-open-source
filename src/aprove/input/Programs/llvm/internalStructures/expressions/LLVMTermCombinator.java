package aprove.input.Programs.llvm.internalStructures.expressions;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Combinator for LLVM terms.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMTermCombinator implements Combinator<LLVMTerm, LLVMTerm, ArithmeticOperationType, LLVMTerm> {

    /**
     * The factory to build terms.
     */
    private final LLVMTermFactory factory;

    /**
     * @param f The factory to build terms.
     */
    public LLVMTermCombinator(LLVMTermFactory f) {
        this.factory = f;
    }

    @Override
    public LLVMTerm combine(ArithmeticOperationType type, LLVMTerm lhs, LLVMTerm rhs) {
        return this.factory.operation(type, lhs, rhs);
    }

}
