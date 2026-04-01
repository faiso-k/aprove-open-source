package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

/**
 * Parsed array type.
 * @author Janine Repke, cryingshadow
 * @version $Id$
 */
public class LLVMParseArrayType extends LLVMParseType {

    /**
     * The type of the elements.
     */
    private LLVMParseType elementType;

    /**
     * The number of elements.
     */
    private LLVMParseLiteral length;

    /**
     * @param elementType The type of the elements.
     * @param length The number of elements.
     */
    public LLVMParseArrayType(LLVMParseType elementType, LLVMParseLiteral length) {
        this.elementType = elementType;
        this.length = length;
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        // array is a derived type and not primitive
        return false;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return false;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        try {
            return
                new LLVMArrayType(
                    // any element type is allowed
                    this.elementType.convertToBasicType(typeDefs, pointerSize),
                    // TODO other values than i64 possible?
                    this.length.convertToBasicLiteral(LLVMIntType.I64, true, typeDefs, pointerSize).toInt()
                );
        } catch (UnsupportedOperationException e) {
            throw new LLVMParseException(e.getMessage());
        }
    }

    /**
     * @return The type of elements.
     */
    public LLVMParseType getElementType() {
        return this.elementType;
    }

    /**
     * @return The number of elements.
     */
    public LLVMParseLiteral getLength() {
        return this.length;
    }

    /**
     * Sets the type of elements.
     * @param elementType The type of elements to set.
     */
    public void setElementType(LLVMParseType elementType) {
        this.elementType = elementType;
    }

    /**
     * Sets the number of elements.
     * @param length The number of elements to set.
     */
    public void setLength(LLVMParseLiteral length) {
        this.length = length;
    }

    @Override
    public String toString() {
        return "[" + this.elementType.toString() + " x " + this.length.toString() + "]";
    }

}
