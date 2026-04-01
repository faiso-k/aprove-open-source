package aprove.input.Programs.llvm.internalStructures.literals.const_expr;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMShuffleVectorConstExpr extends LLVMConstExpr {

    /**
     * The mask vector.
     */
    private final LLVMLiteral maskLiteral;

    /**
     * The first vector.
     */
    private final LLVMLiteral vector1Literal;

    /**
     * The second vector.
     */
    private final LLVMLiteral vector2Literal;

    /**
     * @param type The type of the resulting vector (already computed in parser, so don't create a new object here).
     * @param vec1 The first vector.
     * @param vec2 The second vector.
     * @param mask The mask vector.
     */
    public LLVMShuffleVectorConstExpr(
        final LLVMType type,
        final LLVMLiteral vec1,
        final LLVMLiteral vec2,
        final LLVMLiteral mask)
    {
        super(type);
        // type is already calculated in parser, so re-use it here
        // types of vectors must be equal TODO check this in parser only or also/only here?
        // resulting type is not necessarily equal to vector types (length may vary)
        this.vector1Literal = vec1;
        this.vector2Literal = vec2;
        this.maskLiteral = mask;
    }

    /**
     * @return The mask vector.
     */
    public LLVMLiteral getMaskLiteral() {
        return this.maskLiteral;
    }

    /**
     * @return The first vector.
     */
    public LLVMLiteral getVector1Literal() {
        return this.vector1Literal;
    }

    /**
     * @return The second vector.
     */
    public LLVMLiteral getVector2Literal() {
        return this.vector2Literal;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.literals.BasicLiteral#toDebugString()
     */
    @Override
    public String toDebugString() {
        final StringBuilder strBuilder = new StringBuilder("ShuffleVectorExpr ");
        strBuilder.append(" value1Type: " + this.vector1Literal.getType());
        strBuilder.append(" value1Lit: " + this.vector1Literal);
        strBuilder.append(" value2Type: " + this.vector2Literal.getType());
        strBuilder.append(" value2Lit: " + this.vector2Literal);
        return strBuilder.toString();
    }

}
