package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public abstract class LLVMParseLiteral {

    //    /**
    //     * Each subtype of ParseType has exactly one data type.
    //     *
    //     * These types differ slightly from types in ParseType. For example,
    //     * literals have a type FPHex, which means that the number is a hex
    //     * representation. But the type can be Float or Double. Null is also a
    //     * literal but not a type, the type is pointer.
    //     */
    //    public enum Type { // operation
    //        ARRAY, DOUBLE, FPHEX, FPNORMAL, INT, BIGINT, METADATA, NULL, PACKED_STRUCTURE, VARIABLE, POINTER, STRING, STRUCTURE, UNDEF, VECTOR, VOID, ERROR, ZERO_INITIALIZER, CONST_EXP
    //    }

    //    /**
    //     * The type is a redundant information for faster access.
    //     */
    //    public Type type;
    //
    //    public Literal(Type type) {
    //        this.type = type;
    //    }

    /**
     * @param expectedType TODO
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return TODO
     * @throws LLVMParseException If a parse error occurs.
     */
    public LLVMLiteral convertToAddressSpace(LLVMType expectedType, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        throw new LLVMWrongAddressSpaceTypeException(this);
    }

    /**
     * Converts a literal to an alignment. An alignment is an integer number.
     * For all other types an exception will be thrown.
     * @param pointerSize The pointer size.
     * @return the converted alignment literal.
     * @throws LLVMParseException If a parse error occurs.
     */
    public final LLVMLiteral convertToAlignment(int pointerSize) throws LLVMParseException {
        // TODO i32 just assumed
        return this.convertToBasicLiteral(LLVMIntType.I32, true, null, pointerSize);
    }

    /**
     * Converts a Literal to a BasicLiteral and checks if the expected type and
     * the literal fit together. If not an exception will be thrown.
     * @param expectedType The type of the literal.
     * @param unsigned
     * @param typeDefs Type definitions (just needed for type checks in complex literals).
     * @param pointerSize The pointer size.
     * @return The converted literal
     * @throws LLVMParseException If a parse error occurs.
     */
    public abstract LLVMLiteral convertToBasicLiteral(
        LLVMType expectedType,
        boolean unsigned,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException;

    /**
     * Converts a literal to a variable name. This is only possible for ParseVariableNames or constant expressions
     * which just bitcast a ParseVariableName. For all other literal types, an exception will be thrown. Must be
     * overridden in Literals suitable for conversion into an identifier.
     * @param expectedType The type of the identifier.
     * @return The converted identifier.
     * @throws LLVMWrongVariableNameTypeException If this literal is not suitable for conversion into an identifier.
     */
    public LLVMVariableLiteral convertToIdentifier(LLVMType expectedType) throws LLVMWrongVariableNameTypeException {
        throw new LLVMWrongVariableNameTypeException(this);
    }

    /**
     * Converts a literal to a 32 bit integer. For non-integer types an exception will be thrown.
     * @param pointerSize The pointer size.
     * @return the converted integer literal.
     * @throws LLVMParseException If a parse error occurs.
     */
    public int convertToI32(int pointerSize) throws LLVMParseException {
        return this.convertToBasicLiteral(LLVMIntType.I32, true, null, pointerSize).toInt();
    }

    /**
     * Converts a Literal to a label string. Labels are variable names with local scope.
     * Must be overridden in literals suitable for conversion into a label.
     * @return The converted String.
     * @throws LLVMParseException If a parse error occurs.
     */
    public String convertToLabelName() throws LLVMParseException {
        throw new LLVMWrongLabelTypeException(this);
    }

    /**
     * Converts a literal to a section. A section is a string or variable which represents strings.
     * Must be overridden in literals suitable for conversion into a section String.
     * @return The converted String.
     * @throws LLVMParseException If a parse error occurs.
     */
    public String convertToSection() throws LLVMParseException {
        throw new LLVMWrongSectionTypeException(this);
    }

}
