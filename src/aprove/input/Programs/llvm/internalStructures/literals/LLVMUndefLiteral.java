package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMUndefLiteral extends LLVMLiteral {

    /**
     * @param type The type of the literal.
     */
    public LLVMUndefLiteral(final LLVMType type) {
        super(type);
        // TODO check whether void type or null would be better here
    }

    @Override
    public String toDebugString() {
        return "Undef";
    }

    @Override
    public String toString() {
        return "undef";
    }

}
