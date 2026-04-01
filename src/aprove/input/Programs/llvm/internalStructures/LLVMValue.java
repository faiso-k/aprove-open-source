package aprove.input.Programs.llvm.internalStructures;

import java.math.*;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * @author cryingshadow
 *
 */
public interface LLVMValue extends Immutable {

    /**
     * @return A fresh reference for this value. If this value represents exactly one integer, a constant reference is
     *         returned.
     * @throws UndefinedBehaviorException If the value is a trap value.
     */
    LLVMHeuristicVariable createLLVMRef() throws UndefinedBehaviorException;

    /**
     * @return The only represented integer value if <code>isIntLiteral</code> returns true. Null otherwise.
     * @throws UndefinedBehaviorException If the value is a trap value.
     */
    BigInteger getIntLiteralValue();

    /**
     * @return True iff this object represents exactly one integer value.
     */
    boolean isIntLiteral();

    /**
     * @return This value as AbstractInt. For trap values, this refers to the ordinary value they might be restored to.
     */
    AbstractInt getThisAsAbstractInt();

    /**
     * @return This value as AbstractBoundedInt. For trap values, this refers to the ordinary value they might be
     * restored to.
     */
    AbstractBoundedInt getThisAsAbstractBoundedInt();

}
