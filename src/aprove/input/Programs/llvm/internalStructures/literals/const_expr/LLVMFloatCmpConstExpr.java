package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMFloatCmpConstExpr extends LLVMConstExpr {

    /**
     * The comparison type.
     */
    private final LLVMFloatCmpOpType comparisonCode;

    /**
     * First operand.
     */
    private final LLVMLiteral operand1Value;

    /**
     * Second operand.
     */
    private final LLVMLiteral operand2Value;

    /**
     * @param type The type of the result (boolean, but possibly named).
     * @param op The comparison type.
     * @param val1 First operand.
     * @param val2 Second operand.
     */
    public LLVMFloatCmpConstExpr(LLVMType type, LLVMFloatCmpOpType op, LLVMLiteral val1, LLVMLiteral val2) {
        super(type);
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "Types of operands must be equal!";
        }
        this.comparisonCode = op;
        this.operand1Value = val1;
        this.operand2Value = val2;
    }

    /**
     * @return The comparison type.
     */
    public LLVMFloatCmpOpType getComparisonCode() {
        return this.comparisonCode;
    }

    /**
     * @return First operand.
     */
    public LLVMLiteral getOperand1Value() {
        return this.operand1Value;
    }

    /**
     * @return Second operand.
     */
    public LLVMLiteral getOperand2Value() {
        return this.operand2Value;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("FloatCmpExpr ");
        strBuilder.append(" cmp: " + this.comparisonCode);
        strBuilder.append(" opType: " + this.operand1Value.getType());
        strBuilder.append(" op1Value: " + this.operand1Value);
        strBuilder.append(" op2Value: " + this.operand2Value);
        return strBuilder.toString();
    }

}
