package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMExtractElementConstExpr extends LLVMConstExpr {

    /**
     * The index of the element.
     */
    private final LLVMLiteral indexLiteral;

    /**
     * The vector.
     */
    private final LLVMLiteral vectorLiteral;

    /**
     * @param type The type of the element.
     * @param vector The vector.
     * @param index The index of the element.
     */
    public LLVMExtractElementConstExpr(final LLVMType type, final LLVMLiteral vector, final LLVMLiteral index) {
        super(type);
        this.vectorLiteral = vector;
        this.indexLiteral = index;
    }

    /**
     * @return The index of the element.
     */
    public LLVMLiteral getIndexLiteral() {
        return this.indexLiteral;
    }

    /**
     * @return The vector.
     */
    public LLVMLiteral getVectorLiteral() {
        return this.vectorLiteral;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("ExtactElemntExpr ");
        strBuilder.append(" vectorType: " + this.vectorLiteral.getType());
        strBuilder.append(" vectorLiteral: " + this.vectorLiteral);
        strBuilder.append(" indexLiteral: " + this.indexLiteral);
        return strBuilder.toString();
    }

}
