package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMGetElementPtrConstExpr extends LLVMConstExpr {

    /**
     * Inbounds flag.
     */
    private final boolean inbounds;

    /**
     * The indices.
     */
    private final ImmutableList<LLVMLiteral> indices;

    /**
     * The base pointer.
     */
    private final LLVMLiteral pointerLiteral;

    /**
     * @param type The type of the resulting pointer.
     * @param pointer The base pointer.
     * @param idxs The indices.
     * @param inboundsParam Inbounds flag.
     */
    public LLVMGetElementPtrConstExpr(
        final LLVMType type,
        final LLVMLiteral pointer,
        final ImmutableList<LLVMLiteral> idxs,
        final boolean inboundsParam)
    {
        super(type);
        this.pointerLiteral = pointer;
        this.indices = idxs;
        this.inbounds = inboundsParam;
    }

    /**
     * @return The indices.
     */
    public ImmutableList<LLVMLiteral> getIndices() {
        return this.indices;
    }

    /**
     * @return The base pointer.
     */
    public LLVMLiteral getPointerLiteral() {
        return this.pointerLiteral;
    }

    /**
     * @return Inbounds flag.
     */
    public boolean isInbounds() {
        return this.inbounds;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("GetElemntPtr ");
        strBuilder.append(" ptrType: " + this.pointerLiteral.getType());
        strBuilder.append(" ptrLiteral: " + this.pointerLiteral);
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
