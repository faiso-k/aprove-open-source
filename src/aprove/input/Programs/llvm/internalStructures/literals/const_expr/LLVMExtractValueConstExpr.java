package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMExtractValueConstExpr extends LLVMConstExpr {

    /**
     * The aggregate.
     */
    private final LLVMLiteral aggregateLiteral;

    /**
     * The indices specifying the element.
     */
    private final ImmutableList<LLVMRegularIntLiteral> indices;

    /**
     * @param type The type of the element.
     * @param aggr The aggregate.
     * @param idxs The indices specifying the element.
     */
    public LLVMExtractValueConstExpr(final LLVMType type, final LLVMLiteral aggr, final ImmutableList<LLVMRegularIntLiteral> idxs) {
        super(type);
        this.aggregateLiteral = aggr;
        this.indices = idxs;
    }

    /**
     * @return The aggregate.
     */
    public LLVMLiteral getAggregateLiteral() {
        return this.aggregateLiteral;
    }

    /**
     * @return The indices specifying the element.
     */
    public ImmutableList<LLVMRegularIntLiteral> getindices() {
        return this.indices;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("ExtactElemntExpr ");
        strBuilder.append(" aggrType: " + this.aggregateLiteral.getType());
        strBuilder.append(" aggrLiteral: " + this.aggregateLiteral);
        strBuilder.append(" indexes: (");
        boolean first = true;
        for (final LLVMLiteral index : this.indices) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + index);
        }
        strBuilder.append(")");

        return strBuilder.toString();
    }

}
