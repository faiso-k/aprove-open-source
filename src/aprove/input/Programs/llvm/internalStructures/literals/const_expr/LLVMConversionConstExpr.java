package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMConversionConstExpr extends LLVMConstExpr {

    /**
     * The value to convert.
     */
    private final LLVMLiteral fromLiteral;

    /**
     * The conversion type.
     */
    private final LLVMConvInstrType operation;

    /**
     * @param toType The type to convert the value to.
     * @param op The conversion type.
     * @param fromLit The value to convert.
     */
    public LLVMConversionConstExpr(LLVMType toType, LLVMConvInstrType op, LLVMLiteral fromLit) {
        super(toType);
        this.operation = op;
        this.fromLiteral = fromLit;
    }

    /**
     * @return The value to convert.
     */
    public LLVMLiteral getFromLiteral() {
        return this.fromLiteral;
    }

    /**
     * @return The conversion type.
     */
    public LLVMConvInstrType getOperation() {
        return this.operation;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("ConversionExpr ");
        strBuilder.append(" operator: " + this.operation);
        strBuilder.append(" fromType: " + this.fromLiteral.getType());
        strBuilder.append(" fromLiteral: " + this.fromLiteral);
        strBuilder.append(" toType: " + this.getType());
        return strBuilder.toString();
    }

}
