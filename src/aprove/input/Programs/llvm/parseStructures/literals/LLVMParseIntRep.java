package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseIntRep extends LLVMParseLiteral {

    /**
     * String containing the value, has to be parsed
     */
    private String valueRep;

    public LLVMParseIntRep(String valueRep) {
        this.setValueRep(valueRep);
    }

    @Override
    public LLVMLiteral convertToAddressSpace(LLVMType expectedType, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        // TODO type right?
        // TODO turn NumberFormatException into LLVMParseException?
        return new LLVMRegularIntLiteral(32, Integer.parseInt(this.valueRep), true);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        if (expectedType.isIntType()) {
            final LLVMIntType intType = expectedType.getThisAsIntType();
            // a 64 bit unsigned integer will allready overflow a java long
            if (intType.size() < 64) {
                return new LLVMRegularIntLiteral(expectedType, Long.parseLong(this.valueRep), unsigned);
            } else {
                return new LLVMBigIntLiteral(expectedType, this.valueRep);
            }
        } else {
            throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
        }
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
