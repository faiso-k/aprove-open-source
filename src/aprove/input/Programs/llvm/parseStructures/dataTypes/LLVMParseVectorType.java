package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMParseVectorType extends LLVMParseType {

    private LLVMParseType elementType;
    private LLVMParseLiteral length;

    public LLVMParseVectorType(LLVMParseType elementType, LLVMParseLiteral length) {
        this.elementType = elementType;
        this.length = length;
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        // a vector type is a derived type and so no primitive type
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
                new LLVMVectorType(
                    this.elementType.convertToBasicType(typeDefs, pointerSize),
                    // TODO other types than i64 possible?
                    this.length.convertToBasicLiteral(LLVMIntType.I64, true, typeDefs, pointerSize).toInt()
                );
        } catch (UnsupportedOperationException e) {
            throw new LLVMParseException(e.getMessage());
        }
    }

    public LLVMParseType getElementType() {
        return this.elementType;
    }

    public LLVMParseLiteral getLength() {
        return this.length;
    }

    public void setElementType(LLVMParseType elementType) {
        this.elementType = elementType;
    }

    public void setLength(LLVMParseLiteral length) {
        this.length = length;
    }

    @Override
    public String toString() {
        return "<" + this.elementType.toString() + " x " + this.length.toString() + ">";
    }

}
