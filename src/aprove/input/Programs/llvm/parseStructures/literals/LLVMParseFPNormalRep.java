package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseFPNormalRep extends LLVMParseLiteral {

    /**
     * String containing the value, has to be parsed
     */
    private String valueRep;

    public LLVMParseFPNormalRep(String valueRep) {
        this.setValueRep(valueRep);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        final LLVMType unnamedType = expectedType.getFirstNonNamedType();
        if (unnamedType instanceof LLVMFloatType) {
            // TODO turn NumberFormatExcpetion into LLVMParseException?
            return new LLVMFloatLiteral(expectedType, Float.valueOf(this.valueRep));
        } else if (unnamedType instanceof LLVMDoubleType) {
            return new LLVMDoubleLiteral(expectedType, Double.valueOf(this.valueRep));
        }
        throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
    }

    public String getValueRep() {
        return this.valueRep;
    }

    public void setValueRep(String valueRep) {
        this.valueRep = valueRep;
    }

    @Override
    public String toString() {
        return this.valueRep;
    }

}
