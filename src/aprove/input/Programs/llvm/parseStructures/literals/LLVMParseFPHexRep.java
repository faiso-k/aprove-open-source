package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public class LLVMParseFPHexRep extends LLVMParseLiteral {

    /**
     * hex format of the parsed string
     */
    private LLVMParseHexFormat hexFormat;

    /**
     * String in hexadecimal representation without leading 0x, 0xK ...
     */
    private String valueRep;

    public LLVMParseFPHexRep(String valueRep, LLVMParseHexFormat hexFormat) {
        this.valueRep = valueRep;
        this.hexFormat = hexFormat;
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        final LLVMType unnamedType = expectedType.getFirstNonNamedType();
        if (unnamedType instanceof LLVMDoubleType) {
            if (this.hexFormat == LLVMParseHexFormat.NORMAL) {
                if (this.valueRep.length() != 16) {
                    throw new LLVMWrongHexFormatException(expectedType, this.valueRep);
                }
                try {
                    return new LLVMDoubleLiteral(expectedType, Double.longBitsToDouble(Long.valueOf(this.valueRep, 16)));
                } catch (NumberFormatException e) {
                    throw new LLVMWrongHexFormatException(expectedType, this.valueRep);
                }
            }
        } else if (unnamedType instanceof LLVMFloatType) {
            if (this.hexFormat == LLVMParseHexFormat.NORMAL) {
                if (this.valueRep.length() != 8 && this.valueRep.length() != 16) {
                    throw new LLVMWrongHexFormatException(expectedType, this.valueRep);
                }
                try {
                    if (this.valueRep.length() == 16) {
                        // workaround as long as we cannot handle floats
                        return LLVMFloatLiteral.UNKNOWN;
                        //return new LLVMFloatLiteral(expectedType, Float.intBitsToFloat(Integer.valueOf(this.valueRep, 32)));
                    }
                    return new LLVMFloatLiteral(expectedType, Float.intBitsToFloat(Integer.valueOf(this.valueRep, 16)));
                } catch (NumberFormatException e) {
                    e.printStackTrace();
                    throw new LLVMWrongHexFormatException(expectedType, this.valueRep);
                }
            }
        }
        // incorrect type
        throw new LLVMExpectedTypeDoesNotFitException(expectedType, this);
    }

    public LLVMParseHexFormat getHexFormat() {
        return this.hexFormat;
    }

    public String getValueRep() {
        return this.valueRep;
    }

    public void setHexFormat(LLVMParseHexFormat hexFormat) {
        this.hexFormat = hexFormat;
    }

    public void setValueRep(String valueRep) {
        this.valueRep = valueRep;
    }

    @Override
    public String toString() {
        return this.hexFormat.toString() + " " + this.valueRep;
    }

}
