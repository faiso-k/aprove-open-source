package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;

/**
 * @author Janine Repke, CryingShadow
 * TODO check documentation
 */
public class LLVMBinaryConstExpr extends LLVMConstExpr {

    /**
     * defines exact operation, but should only be used for udiv, sdiv, lshr or ashr opertion type
     */
    private final boolean exact;

    /**
     * not needed for all operation types, e.g. is not needed for fmul, fsub ...
     */
    private final boolean nsw;

    /**
     * not needed for all operation types, e.g. is not needed for fmul, fsub ...
     */
    private final boolean nuw;

    /**
     * First operand.
     */
    private final LLVMLiteral operand1Value;

    /**
     * Second operand.
     */
    private final LLVMLiteral operand2Value;

    /**
     * Operation type.
     */
    private final LLVMBinaryOpType operator;

    /**
     * @param resType Type of the result.
     * @param op Operation type.
     * @param val1 First operand.
     * @param val2 Second operand.
     * @param exactParam Exact parameter. TODO
     * @param nuwParam NUW parameter. TODO
     * @param nswParam NSW parameter. TODO
     */
    public LLVMBinaryConstExpr(
        LLVMType resType,
        LLVMBinaryOpType op,
        LLVMLiteral val1,
        LLVMLiteral val2,
        boolean exactParam,
        boolean nuwParam,
        boolean nswParam
    ) {
        super(resType);
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "Types of operands must be equal!";
        }
        this.operator = op;
        this.operand1Value = val1;
        this.operand2Value = val2;
        this.exact = exactParam;
        this.nuw = nuwParam;
        this.nsw = nswParam;
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

    /**
     * @return Operation type.
     */
    public LLVMBinaryOpType getOperator() {
        return this.operator;
    }

    /**
     * @return Exact parameter.
     */
    public boolean isExact() {
        return this.exact;
    }

    /**
     * @return NSW parameter.
     */
    public boolean isNsw() {
        return this.nsw;
    }

    /**
     * @return NUW parameter.
     */
    public boolean isNuw() {
        return this.nuw;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("BinaryExpr ");
        strBuilder.append(" operator: " + this.operator);
        strBuilder.append(" nuw: " + this.nuw);
        strBuilder.append(" nsw: " + this.nsw);
        strBuilder.append(" opType: " + this.operand1Value.getType());
        strBuilder.append(" op1Value: " + this.operand1Value);
        strBuilder.append(" op2Value: " + this.operand2Value);
        return strBuilder.toString();
    }

}
