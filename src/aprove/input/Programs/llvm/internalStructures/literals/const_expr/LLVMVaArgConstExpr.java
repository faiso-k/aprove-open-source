package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMVaArgConstExpr extends LLVMConstExpr {

    /**
     * The variable argument list.
     */
    private final LLVMLiteral vaArgList;

    /**
     * @param type The type of the argument to choose from the argument list.
     * @param list The variable argument list.
     */
    public LLVMVaArgConstExpr(final LLVMType type, final LLVMLiteral list) {
        super(type);
        this.vaArgList = list;
    }

    /**
     * @return The variable argument list.
     */
    public LLVMLiteral getVaArgList() {
        return this.vaArgList;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("ShuffleVectorExpr ");
        strBuilder.append(" vaArgType: " + this.vaArgList.getType());
        strBuilder.append(" vaArgValue: " + this.vaArgList);
        strBuilder.append(" argumentType: " + this.getType());
        return strBuilder.toString();
    }

}
