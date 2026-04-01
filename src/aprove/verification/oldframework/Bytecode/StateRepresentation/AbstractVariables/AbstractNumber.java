package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Representation of number values in our symbolic interpretation.
 * @author Marc Brockschmidt, cryingshadow
 */
public abstract class AbstractNumber extends AbstractVariable implements LLVMValue {

    /**
     * @return this
     */
    @Override
    public AbstractVariable clone() {
        return this;
    }

    @Override
    public LLVMHeuristicVariable createLLVMRef() {
        if (this.isIntLiteral()) {
            return LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY.constant(this.getIntLiteralValue());
        }
        return LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY.freshVariable();
    }

    @Override
    public BigInteger getIntLiteralValue() {
        // This method should be overridden in all classes representing only one integer value!
        return null;
    }

    @Override
    public AbstractBoundedInt getThisAsAbstractBoundedInt() {
        return (AbstractBoundedInt)this;
    }

    @Override
    public AbstractInt getThisAsAbstractInt() {
        return (AbstractInt)this;
    }

    /**
     * Intersect this abstract number the other abstract number.
     * @param other the other abstract number to intersect with
     * @return the intersected value
     * @throws IntersectionFailException if the intersection is empty
     */
    public abstract AbstractNumber intersect(final AbstractNumber other) throws IntersectionFailException;

    @Override
    public boolean isIntLiteral() {
        // This method should be overridden in all classes representing only one integer value!
        return false;
    }

    /**
     * @return true iff this AbstractNumber represents exactly one value.
     */
    public abstract boolean isLiteral();

    /**
     * @return false, because a primitive never is the NULL instance.
     */
    @Override
    public boolean isNULL() {
        return false;
    }

    /**
     * @param ref reference whose value we are
     * @return A sequence of integer relations (in S-Expression format) expressing the information we have about <code>ref</code>
     */
    public abstract Collection<String> toSExpStrings(final AbstractVariableReference ref);

}
