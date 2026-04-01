package aprove.input.Programs.llvm.internalStructures.literals;

import aprove.input.Programs.llvm.internalStructures.dataType.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMNullLiteral extends LLVMLiteral {

    /**
     * @param type The type.
     */
    public LLVMNullLiteral(final LLVMType type) {
        super(type);
        // TODO check whether void or null would be better here
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final String str = "BasicNullLiteral";
        return str;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "null";
    }

}
