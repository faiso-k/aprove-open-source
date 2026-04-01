package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * A string is no identifier name, identifiers have a percent or dollar sign as prefix.
 * @author Janine Repke, CryingShadow
 */
public class LLVMParseStringLiteral extends LLVMParseLiteral {

    private final String stringValue;

    public LLVMParseStringLiteral(String str) {
        this.stringValue = str;
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
        throws LLVMParseException
    {
        // TODO check whether a conversion from ParseString to BasicString is meaningful
        if (expectedType.getFirstNonNamedType() instanceof LLVMArrayType) {
            final LLVMArrayType arrayType = (LLVMArrayType) expectedType.getFirstNonNamedType();
            if (arrayType.getElementType().isIntType()) {
                final LLVMIntType elementType = arrayType.getElementType().getThisAsIntType();
                if (elementType.size() == 8) {
                    return new LLVMStringLiteral(this.stringValue);
                }
            }
        }
        if (expectedType.isPointerType()) {
            final LLVMPointerType pointerType = expectedType.getThisAsPointerType();
            if (pointerType.getTargetType().isIntType()) {
                final LLVMIntType elementType = (LLVMIntType) pointerType.getTargetType();
                if (elementType.size() == 8) {
                    return new LLVMStringLiteral(this.stringValue);
                }
            }
        }
        throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
    }

    @Override
    public String convertToSection() throws LLVMParseException {
        return this.stringValue;
    }

    public String getStringValue() {
        return this.stringValue;
    }

    @Override
    public String toString() {
        return this.stringValue;
    }

}
