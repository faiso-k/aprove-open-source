package aprove.input.Programs.llvm.parseStructures.dataTypes;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

public abstract class LLVMParseType {

    /**
     * All data types which can occur in a LLVM file. Each subtype of ParseType
     * has exactly one enum type.
     *
     * These types differ slightly from types in Literal. For example, literals
     * have a type FPHex, which means that the number is a hex representation.
     * But the type can be Float or Double. Null is also a literal but not a
     * type, the type is pointer.
     */
    //    public enum Type {
    //        ARRAY,
    //        DOUBLE,
    //        FLOAT,
    //        FP128,
    //        FUNCTION,
    //        INT,
    //        LABEL,
    //        METADATA,
    //        NAMED,
    //        OPAQUE,
    //        PACKED_STRUCTURE,
    //        POINTER,
    //        PPC_FP128,
    //        STRING,
    //        STRUCTURE,
    //        VALIST,
    //        VECTOR,
    //        VOID,
    //        X86_FP80
    //    }

    /**
     * The type is a redundant information for faster access.
     */
    //    public Type type;

    //    public ParseType(final Type type) {
    //        this.type = type;
    //    }

    public boolean checkIfTypeIsIntType(final LLVMModule basicModule) throws LLVMParseException {
        return false;
    }

    public abstract boolean checkIfTypeIsPrimitiveType(final LLVMParseModule module);

    /**
     * Returns true iff the type is a float or integer type. Other types are not
     * allowed as vector elements.
     */
    abstract public boolean checkifTypeIsVectorElementType(final LLVMParseModule module);

    /**
     * This function creates from this ParseType a BasicType and also checks if
     * correct types are used.
     * @param typeDefs Type definitions.
     * @param pointerSize The size of pointers.
     */
    abstract public LLVMType convertToBasicType(final Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException;

    //    public Type getType() {
    //        return this.type;
    //    }

    public boolean isStringType(final LLVMParseModule module) {
        //        switch (this.getType()) {
        //        case ARRAY: // a string can be represented as array with i8 types
        //            final ArrayType array = (ArrayType) this;
        //            final ParseType element = array.getElementType();
        //            if (element != null && element.getType() == Type.INT) {
        //                final IntType intType = (IntType) element;
        //                if (intType.getNumberOfBytes() == 8) {
        //                    return true;
        //                }
        //            }
        //            break;
        //        case POINTER: // a string can be represented as pointer with i8 types
        //            final PointerType pointer = (PointerType) this;
        //            final ParseType target = pointer.getTargetType();
        //            if (target != null && target.getType() == Type.INT) {
        //                final IntType intType = (IntType) target;
        //                if (intType.getNumberOfBytes() == 8) {
        //                    return true;
        //                }
        //            }
        //            break;
        //        case NAMED: // look up type which will be named
        //            final NamedType named = (NamedType) this;
        //            final ParseType targetType = module.getTypeDefinition(named.getTypeName());
        //            return targetType.isStringType(module);
        //        }
        return false;
    }

}
