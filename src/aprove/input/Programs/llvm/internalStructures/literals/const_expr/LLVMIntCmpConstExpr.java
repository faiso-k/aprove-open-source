package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMIntCmpConstExpr extends LLVMConstExpr {

    /**
     * The comparison type.
     */
    private final LLVMIntCmpOpType comparisonCode;

    /**
     * The first operand.
     */
    private final LLVMLiteral operand1Value;

    /**
     * The second operand.
     */
    private final LLVMLiteral operand2Value;

    /**
     * @param type The type of the result (boolean, but possibly named - TODO true?).
     * @param operation The comparison type.
     * @param val1 The first operand.
     * @param val2 The second operand.
     */
    public LLVMIntCmpConstExpr(LLVMType type, LLVMIntCmpOpType operation, LLVMLiteral val1, LLVMLiteral val2) {
        super(type);
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "The types of the values must be equal!";
        }
        this.comparisonCode = operation;
        this.operand1Value = val1;
        this.operand2Value = val2;
    }

    /**
     * @return The comparison type.
     */
    public LLVMIntCmpOpType getComparisonCode() {
        return this.comparisonCode;
    }

    /**
     * @return the first operand.
     */
    public LLVMLiteral getOperand1Value() {
        return this.operand1Value;
    }

    /**
     * @return The second operand.
     */
    public LLVMLiteral getOperand2Value() {
        return this.operand2Value;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("IntCmpExpr ");
        strBuilder.append(" cmp: " + this.comparisonCode);
        strBuilder.append(" opType: " + this.operand1Value.getType());
        strBuilder.append(" op1Value: " + this.operand1Value);
        strBuilder.append(" op2Value: " + this.operand2Value);
        return strBuilder.toString();
    }

}
