package aprove.input.Programs.llvm.internalStructures.expressions;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * LLVMTerms also need to be converted to TRSTerms.
 * @author cryingshadow
 * @version $Id$
 */
public interface LLVMTerm extends FunctionalIntegerExpression, TRSTermExpressible {

//    /**
//     * @return An SMTLIB value corresponding to this node.
//     */
//    SMTLIBIntValue toSMTIntValue();

    /**
     * @param term Some LLVMTerm.
     * @param factory A term factory.
     * @return The negated term.
     */
    public static LLVMTerm negate(LLVMTerm term, LLVMTermFactory factory) {
        return factory.mult(factory.negone(), term);
    }

    /**
     * @param factory A factory to build terms.
     * @return If this term only consists of constants, the constant to which this term evaluates is returned. Null
     *         otherwise.
     * @throws DivisionByZeroException If this term contains a division by zero.
     */
    LLVMConstant evaluate(LLVMTermFactory factory) throws DivisionByZeroException;

    /**
     * @return A factory for building terms.
     */
    default LLVMTermFactory getTermFactory() {
        return LLVMDefaultTermFactory.LLVM_DEFAULT_TERM_FACTORY;
    }

    @Override
    Set<? extends LLVMSymbolicVariable> getVariables();

    @Override
    LLVMTerm negate();

}
