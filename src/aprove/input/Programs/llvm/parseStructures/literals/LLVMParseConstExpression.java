package aprove.input.Programs.llvm.parseStructures.literals;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.literals.const_expr.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 * The methods in this class convert a constant expression from the parsing structures to a constant expression
 * in basic structures (the basic structures are structures to work with).
 * The constant expression in the parsing structures is a list of objects which is constructed
 * in the parser and has to be interpreted in the right manner (which will be done in the methods of this class).
 * So if you change the grammar for constant expressions in the parser, you also have to change
 * the object interpretation in this class.
 * TODO build in more checks w.r.t. the types!
 */
public class LLVMParseConstExpression extends LLVMParseLiteral {

    /**
     * Checks if the binary operation is of type udiv, sdiv, lshr or ashr. Only these operation types can be
     * used with the exact specifier. This function is used in the parser instead of directly checking this
     * property with the parse grammar, which would make the grammar more complex and more complicated to read.
     * @param binaryOpType The binary operation.
     * @return True iff the binary operation is of type udiv, sdiv, lshr or ashr.
     */
    public static boolean isBinaryOpExactCompatible(LLVMBinaryOpType binaryOpType) {
        switch (binaryOpType) {
            case ASHR:
            case LSHR:
            case SDIV:
            case UDIV:
                // these binary op types can be used with the exact speicifer
                return true;
            default:
                return false;
        }
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted binary constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToBinaryConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // binary operator
        LLVMBinaryOpType operationType = ((LLVMBinaryOpType)objIt.next());
        // exact
        boolean exact = (Boolean)objIt.next();
        // nuw
        boolean nuw = (Boolean)objIt.next();
        // nsw
        boolean nsw = (Boolean)objIt.next();
        // operand type
        LLVMType operandType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (expectedType.equals(operandType)) : "Expected type does not match specified type!";
        }
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        return new LLVMBinaryConstExpr(operandType, operationType, op1, op2, exact, nuw, nsw);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted conversion constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToConversionConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // operation type
        LLVMConvInstrType operationType = (LLVMConvInstrType)objIt.next();
        // from type
        LLVMType fromType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // from value
        LLVMLiteral fromVal = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(fromType, false, typeDefs, pointerSize);
        // to type
        LLVMType toType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (toType.equals(expectedType)) : "Expected type does not match specified type!";
        }
        return new LLVMConversionConstExpr(toType, operationType, fromVal);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted extract element constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToExtractElementConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (vecType.isVectorType()) : "Vector is no vector!";
            assert (expectedType.equals(vecType.getThisAsVectorType().getElementType())) :
                "Expected type does not match specified type!";
        }
        // vector literal
        LLVMLiteral vector = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // index type - should be i32
        LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (indexType.isIntTypeOfSize(32)) : "Index is no i32!";
        }
        // index literal
        LLVMLiteral index = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize);
        return new LLVMExtractElementConstExpr(expectedType, vector, index);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted extract value constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToExtractValueConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // aggregate type
        LLVMType aggrType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // aggregate literal
        LLVMLiteral aggregate = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(aggrType, false, typeDefs, pointerSize);
        // index type (not specified in the manual, assumed to be i32 TODO check)
        LLVMType indexType = LLVMIntType.I32;
        // index values
        int numOfIndices = (Integer)objIt.next();
        List<LLVMRegularIntLiteral> indices = new ArrayList<LLVMRegularIntLiteral>();
        for (int i = 0; i < numOfIndices; i++) {
            // next index
            indices.add(
                (LLVMRegularIntLiteral)((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize)
            );
        }
        return new LLVMExtractValueConstExpr(expectedType, aggregate, ImmutableCreator.create(indices));
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted float compare constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToFloatCmpConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        if (Globals.useAssertions) {
            assert (expectedType.isBooleanType()) : "Expected type is no boolean!";
        }
        // comparison type
        LLVMFloatCmpOpType operationType = (LLVMFloatCmpOpType)objIt.next();
        // operand type
        LLVMType operandType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        return new LLVMFloatCmpConstExpr(expectedType, operationType, op1, op2);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted GEP constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToGetElementPtrConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // inbounds?
        boolean inbounds = (Boolean)objIt.next();
        // pointer type
        LLVMType pointerType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // pointer literal
        LLVMLiteral pointer = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(pointerType, true, typeDefs, pointerSize);
        // indices
        List<LLVMLiteral> indices = new ArrayList<LLVMLiteral>();
        LLVMParseConstExpression.parseEvenNumberOfIndexObjects(objIt, typeDefs, indices, pointerSize);
//        if (Globals.useAssertions) {
//            assert (
//                expectedType.equals(
//                    new LLVMPointerType(
//                        pointerType.getThisAsPointerType().getTargetType().getSubtype(
//                            indices.subList(1, indices.size())
//                        ),
//                        pointerType.size(),
//                        null
//                    )
//                )
//            ) : "Expected type does not match computed type!";
//        }
        return new LLVMGetElementPtrConstExpr(expectedType, pointer, ImmutableCreator.create(indices), inbounds);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted insert element constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToInsertElementConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // vector literal
        LLVMLiteral vector = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // element type
        LLVMType elemType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // element literal
        LLVMLiteral element = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(elemType, false, typeDefs, pointerSize);
        // index type - should be i32
        LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (indexType.isIntTypeOfSize(32)) : "Index is no i32!";
            assert (expectedType.equals(vecType)) : "Expected type does not match specified type!";
        }
        // index literal
        LLVMRegularIntLiteral index =
            (LLVMRegularIntLiteral)((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize);
        return new LLVMInsertElementConstExpr(vector, element, index);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted insert value constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToInsertValueConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // aggregate type
        LLVMType aggrType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (expectedType.equals(aggrType)) : "Expected type does not match specified type!";
        }
        // aggregate literal
        LLVMLiteral aggregate = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(aggrType, false, typeDefs, pointerSize);
        // element type
        LLVMType elemType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // element literal
        LLVMLiteral element = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(elemType, false, typeDefs, pointerSize);
        // indices
        List<LLVMLiteral> indices = new ArrayList<LLVMLiteral>();
        LLVMParseConstExpression.parseEvenNumberOfIndexObjects(objIt, typeDefs, indices, pointerSize);
        return new LLVMInsertValueConstExpr(aggregate, element, ImmutableCreator.create(indices));
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted integer compare constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToIntCmpConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        if (Globals.useAssertions) {
            assert (expectedType.isBooleanType()) : "Expected type is no boolean!";
        }
        // comparison type
        LLVMIntCmpOpType operationType = (LLVMIntCmpOpType)objIt.next();
        // operand type
        LLVMType operandType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(operandType, false, typeDefs, pointerSize);
        return new LLVMIntCmpConstExpr(expectedType, operationType, op1, op2);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted select constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToSelectConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // condition type
        LLVMType conditionType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // condition value
        LLVMLiteral condition = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(conditionType, false, typeDefs, pointerSize);
        // first value type
        LLVMType valType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (expectedType.equals(valType)) : "Expected type does not match specified type!";
        }
        // first value
        LLVMLiteral val1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType, false, typeDefs, pointerSize);
        // second value type (must be the same as the first value type)
        LLVMType valType2 = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // second value
        LLVMLiteral val2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType2, false, typeDefs, pointerSize);
        // equality of value types is checked in constructor of SelectExpr
        return new LLVMSelectConstExpr(condition, val1, val2);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted shufflevector constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToShuffleVectorConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // first vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first vector literal
        LLVMLiteral vec1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // second vector type
        LLVMType vecType2 = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (vecType.equals(vecType2)) : "Vectors do not have the same type!";
        }
        // second vector literal
        LLVMLiteral vec2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // mask type
        LLVMType maskType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // mask literal
        LLVMLiteral mask = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(maskType, false, typeDefs, pointerSize);
        // TODO check match of expected type
        return new LLVMShuffleVectorConstExpr(expectedType, vec1, vec2, mask);
    }

    /**
     * @param expectedType The type this expression should have.
     * @param objIt Iterator through the objects of this expression.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted va_arg constant expression.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static LLVMLiteral convertToVaArgConstExpr(
        LLVMType expectedType,
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // type of variable argument list
        LLVMType listType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // variable argument list
        LLVMLiteral argList = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(listType, false, typeDefs, pointerSize);
        // argument type which will be returned
        LLVMType argType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (expectedType.equals(argType)) : "Expected type does not match specified type!";
        }
        return new LLVMVaArgConstExpr(expectedType, argList);
    }

    /**
     * @param objIt The object iterator.
     * @param typeDefs The type definitions.
     * @param indices The indices.
     * @param pointerSize The pointer size.
     * @throws LLVMParseException If a parse error occurs.
     */
    private static void parseEvenNumberOfIndexObjects(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        List<LLVMLiteral> indices,
        int pointerSize
    ) throws LLVMParseException {
        int numOfIndexObjs = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numOfIndexObjs % 2 == 0) : "Number of index objects is not even!";
        }
        for (int i = 0; i < numOfIndexObjs / 2; i++) {
            // index type
            LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            // index literal
            indices.add(((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize));
        }
    }

    /**
     * The object list of this constant expression.
     */
    private final List<Object> objects;

    /**
     * The operation type of this constant expression.
     */
    private final LLVMConstExprType opType;

    /**
     * Creates a constant expression with an empty object list.
     * @param operationType The operation type of this constant expression.
     */
    public LLVMParseConstExpression(LLVMConstExprType operationType) {
        this.opType = operationType;
        this.objects = new ArrayList<Object>();
    }

    /**
     * Adds an object to this expression's object list.
     * @param param The object to add.
     */
    public void addParam(Object param) {
        this.objects.add(param);
    }

    @Override
    public LLVMLiteral convertToAddressSpace(LLVMType expectedType, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        //TODO why this type?
        return this.convertToBasicLiteral(LLVMIntType.I32, true, typeDefs, pointerSize);
    }

    @Override
    public LLVMLiteral convertToBasicLiteral(LLVMType expectedType, boolean unsigned, Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        switch (this.opType) {
            case BINARY:
                return
                    LLVMParseConstExpression.convertToBinaryConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case CONVERSION:
                return
                    LLVMParseConstExpression.convertToConversionConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case EXTRACT_ELEMENT:
                return
                    LLVMParseConstExpression.convertToExtractElementConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case EXTRACT_VALUE:
                return
                    LLVMParseConstExpression.convertToExtractValueConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case FLOAT_CMP:
                return
                    LLVMParseConstExpression.convertToFloatCmpConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case GET_ELEMENT_PTR:
                return
                    LLVMParseConstExpression.convertToGetElementPtrConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case INSERT_ELEMENT:
                return
                    LLVMParseConstExpression.convertToInsertElementConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case INSERT_VALUE:
                return
                    LLVMParseConstExpression.convertToInsertValueConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case INT_CMP:
                return
                    LLVMParseConstExpression.convertToIntCmpConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case SELECT:
                return
                    LLVMParseConstExpression.convertToSelectConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case SHUFFLE_VECTOR:
                return
                    LLVMParseConstExpression.convertToShuffleVectorConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            case VAARG:
                return
                    LLVMParseConstExpression.convertToVaArgConstExpr(
                        expectedType,
                        this.objects.iterator(),
                        typeDefs,
                        pointerSize
                    );
            default:
                throw new LLVMNotYetSupportedException(this.opType);
        }
    }

    @Override
    public LLVMVariableLiteral convertToIdentifier(LLVMType expectedType) throws LLVMWrongVariableNameTypeException {
        if (this.opType == LLVMConstExprType.CONVERSION && this.objects.size() == 4) {
            Object varname = this.objects.get(2);
            if (varname instanceof LLVMParseVariableLiteral) {
                return ((LLVMParseVariableLiteral)varname).convertToIdentifier(expectedType);
            }
        }
        throw new LLVMWrongVariableNameTypeException(this);
    }

    @Override
    public String toString() {
        return "const expr " + this.opType.toString() + " " + this.objects.toString();
    }

}
