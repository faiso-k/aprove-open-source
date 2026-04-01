package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.literals.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMInsertElementConstExpr extends LLVMConstExpr {

    /**
     * The element to insert.
     */
    private final LLVMLiteral elementLiteral;

    /**
     * The index where to insert the element.
     */
    private final LLVMRegularIntLiteral indexLiteral;

    /**
     * The vector.
     */
    private final LLVMLiteral vectorLiteral;

    /**
     * @param vector The vector.
     * @param element The element to insert.
     * @param index The index where to insert the element.
     */
    public LLVMInsertElementConstExpr(final LLVMLiteral vector, final LLVMLiteral element, final LLVMRegularIntLiteral index) {
        super(vector.getType());
        this.vectorLiteral = vector;
        this.elementLiteral = element;
        this.indexLiteral = index;
    }

    /**
     * @return The element to insert.
     */
    public LLVMLiteral getElementLiteral() {
        return this.elementLiteral;
    }

    /**
     * @return the index where to insert the element.
     */
    public LLVMRegularIntLiteral getIndexLiteral() {
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
        final StringBuilder strBuilder = new StringBuilder("InsertElementExpr ");
        strBuilder.append(" vectorType: " + this.vectorLiteral.getType());
        strBuilder.append(" vectorLiteral: " + this.vectorLiteral);
        strBuilder.append(" elementType: " + this.elementLiteral.getType());
        strBuilder.append(" elementLiteral: " + this.elementLiteral);
        strBuilder.append(" indexLiteral: " + this.indexLiteral);
        return strBuilder.toString();
    }

}
