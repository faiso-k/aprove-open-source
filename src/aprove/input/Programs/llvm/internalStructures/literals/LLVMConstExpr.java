package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 */
public abstract class LLVMConstExpr extends LLVMLiteral {

    /**
     * @param type The type.
     */
    protected LLVMConstExpr(final LLVMType type) {
        super(type);
    }

}
