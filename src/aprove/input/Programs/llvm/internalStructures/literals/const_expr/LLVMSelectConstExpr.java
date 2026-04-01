package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMSelectConstExpr extends LLVMConstExpr {

    /**
     * The condition.
     */
    private final LLVMLiteral conditionLiteral;

    /**
     * The value for a true condition.
     */
    private final LLVMLiteral value1Literal;

    /**
     * The value for a false condition.
     */
    private final LLVMLiteral value2Literal;

    /**
     * @param condition The condition.
     * @param val1 The value for a true condition.
     * @param val2 The value for a false condition.
     */
    public LLVMSelectConstExpr(final LLVMLiteral condition, final LLVMLiteral val1, final LLVMLiteral val2) {
        super(val1.getType());
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "The types of selection values must be equal!";
        }
        this.conditionLiteral = condition;
        this.value1Literal = val1;
        this.value2Literal = val2;
    }

    /**
     * @return The condition.
     */
    public LLVMLiteral getConditionLiteral() {
        return this.conditionLiteral;
    }

    /**
     * @return The value for a true condition.
     */
    public LLVMLiteral getValue1Literal() {
        return this.value1Literal;
    }

    /**
     * @return the value for a false condition.
     */
    public LLVMLiteral getValue2Literal() {
        return this.value2Literal;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("SelectExpr ");
        strBuilder.append(" cond: " + this.conditionLiteral.getType());
        strBuilder.append(" condLit: " + this.conditionLiteral);
        strBuilder.append(" valueType: " + this.getType());
        strBuilder.append(" value1Lit: " + this.value1Literal);
        strBuilder.append(" value2Lit: " + this.value2Literal);
        return strBuilder.toString();
    }

}
