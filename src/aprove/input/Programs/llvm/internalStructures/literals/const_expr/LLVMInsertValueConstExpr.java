package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.literals.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMInsertValueConstExpr extends LLVMConstExpr {

    /**
     * The aggregate.
     */
    private final LLVMLiteral aggregateLiteral;

    /**
     * The element to insert.
     */
    private final LLVMLiteral elementLiteral;

    /**
     * The indices specifying where to insert the element.
     */
    private final ImmutableList<LLVMLiteral> indices;

    /**
     * @param aggr The aggregate.
     * @param element The element to insert.
     * @param idxs The indices specifying where to insert the element.
     */
    public LLVMInsertValueConstExpr(final LLVMLiteral aggr, final LLVMLiteral element, final ImmutableList<LLVMLiteral> idxs)
    {
        super(aggr.getType());
        this.aggregateLiteral = aggr;
        this.elementLiteral = element;
        // TODO check possible types for indices - maybe BasicInt is more suitable than BasicLiteral
        this.indices = idxs;
    }

    /**
     * @return The aggregate.
     */
    public LLVMLiteral getAggregateLiteral() {
        return this.aggregateLiteral;
    }

    /**
     * @return The element to insert.
     */
    public LLVMLiteral getElementLiteral() {
        return this.elementLiteral;
    }

    /**
     * @return The indices specifying where to insert the element.
     */
    public ImmutableList<LLVMLiteral> getindices() {
        return this.indices;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("InsertValueExpr ");
        strBuilder.append(" aggrType: " + this.aggregateLiteral.getType());
        strBuilder.append(" aggrLiteral: " + this.aggregateLiteral);
        strBuilder.append(" elementType: " + this.elementLiteral.getType());
        strBuilder.append(" elementLiteral: " + this.elementLiteral);
        strBuilder.append(" indices: (");
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
