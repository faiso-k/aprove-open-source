package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * Type for integers.
 * @author Janine Repke, cryingshadow
 * @version $Id$
 */
public class LLVMParseIntType extends LLVMParseType {

    /**
     * this info specifies the bitwidth of this type (i32 => integer with 32 bits)
     */
    private int numberOfBits;

    /**
     * @param numOfBits The number of bits.
     */
    public LLVMParseIntType(int numOfBits) {
        this.numberOfBits = numOfBits;
    }

    @Override
    public boolean checkIfTypeIsIntType(LLVMModule basicModule) {
        return true;
    }

    @Override
    public boolean checkIfTypeIsPrimitiveType(LLVMParseModule module) {
        return true;
    }

    @Override
    public boolean checkifTypeIsVectorElementType(LLVMParseModule module) {
        return true;
    }

    @Override
    public LLVMType convertToBasicType(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        return new LLVMIntType(this.numberOfBits);
    }

    /**
     * @return The number of bits.
     */
    public int getNumberOfBits() {
        return this.numberOfBits;
    }

    /**
     * @param numOfBits The number of bits.
     */
    public void setNumberOfBits(int numOfBits) {
        this.numberOfBits = numOfBits;
    }

    @Override
    public String toString() {
        return "i" + this.numberOfBits;
    }

}
