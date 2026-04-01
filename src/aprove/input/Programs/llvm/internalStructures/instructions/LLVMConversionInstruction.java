package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.BigInteger;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of conversion instructions in LLVM IR.
 *
 * @author Janine Repke, Marc Brockschmidt, cryingshadow, Jera Hensel
 */
public class LLVMConversionInstruction extends LLVMAssignmentInstruction {

    /**
     * @param state The current state.
     * @param varName The name of the result program variable.
     * @param fromRef The simple term corresponding to the value to convert.
     * @param toType The new type after conversion.
     * @param useBoundedIntegers Use bounded integers?
     * @return The specified state where the specified program variable has a fresh symbolic variable assigned. We only
     *         know that this fresh variable is inside its type bounds.
     */
    private static Set<LLVMSymbolicEvaluationResult> havoc(
        LLVMAbstractState state,
        String varName,
        LLVMSimpleTerm fromRef,
        LLVMType toType,
        boolean useBoundedIntegers,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final Set<LLVMRelation> change = new LinkedHashSet<LLVMRelation>();
        final LLVMAbstractState res = state.assign(varName, null, toType, change, aborter);
        if (useBoundedIntegers) {
            boolean unsigned = state.getModule().getUnsignedBitvectorVariables().contains(varName);
            final IntegerType integerType = toType.getIntegerType(unsigned, true);
            final LLVMSymbolicVariable var = res.getSymbolicVariableForProgramVariable(varName);
            change.add(relationFactory.lessThanEquals(termFactory.constant(integerType.getLower().getConstant()), var));
            change.add(relationFactory.lessThanEquals(var, termFactory.constant(integerType.getUpper().getConstant())));
        }
        return Collections.singleton(new LLVMSymbolicEvaluationResult(res, change));
    }

    /**
     * @param state The current state.
     * @param varName The name of the result program variable.
     * @param fromRef The simple term corresponding to the value to convert.
     * @param toType The old type before conversion.
     * @param toType The new type after conversion.
     * @return The specified state where the specified program variable has assigned a variable with the same value as
     *         the original one.
     */
    private static Set<LLVMSymbolicEvaluationResult> noChange(
        LLVMAbstractState state,
        String varName,
        LLVMSimpleTerm fromRef,
        LLVMType fromType,
        LLVMType toType,
        Abortion aborter
    ) {
        final Set<LLVMRelation> change = new LinkedHashSet<LLVMRelation>();
        LLVMAbstractState res = state.assign(varName, fromRef, toType, change, aborter);
        final boolean useBoundedIntegers = state.getStrategyParamters().useBoundedIntegers;
        if (fromType.size() < toType.size() && useBoundedIntegers) {
            LLVMRelationFactory relFactory = state.getRelationFactory();
            LLVMTermFactory termFactory = relFactory.getTermFactory();
            LLVMSymbolicVariable symVar = res.getSymbolicVariableForProgramVariable(varName);
            BigInteger lower = fromType.getIntegerType(false, true).getLower().getConstant();
            LLVMRelation lowerBoundRel = relFactory.lessThanEquals(termFactory.constant(lower), symVar);
            change.add(lowerBoundRel);
            BigInteger upper = fromType.getIntegerType(false, true).getUpper().getConstant();
            LLVMRelation upperBoundRel = relFactory.lessThanEquals(symVar, termFactory.constant(upper));
            change.add(upperBoundRel);
            res = res.addRelation(lowerBoundRel, aborter);
            res = res.addRelation(upperBoundRel, aborter);
        }
        return
            Collections.singleton(
                new LLVMSymbolicEvaluationResult(res, change)
            );
    }

    /**
     * The literal to convert.
     */
    private final LLVMLiteral fromLiteral;

    /**
     * The type of the conversion to perform.
     */
    private final LLVMConvInstrType typeOfConversion;

    /**
     * @param id The variable to be assigned.
     * @param from The literal to convert.
     * @param convType The type of the conversion to perform.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMConversionInstruction(LLVMVariableLiteral id, LLVMLiteral from, LLVMConvInstrType convType, int debugLine) {
        super(id, debugLine);
        this.fromLiteral = from;
        this.typeOfConversion = convType;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.fromLiteral);
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        // TODO
        return null;
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        // TODO
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        // TODO re-implement refinement for bounded integers
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final boolean useBoundedIntegers = state.getStrategyParamters().useBoundedIntegers;
        final LLVMType toType = this.getIdentifier().getType();
        final LLVMSimpleTerm fromRef = state.getSimpleTermForLiteral(this.fromLiteral);
        final LLVMType fromType = this.fromLiteral.getType();
        final String varName = this.getIdentifier().getName();
        if (state.isPossiblyTrapValue(fromRef)) {
            throw new TrapValueException(nodeNumber);
        }
        LLVMAbstractState res = state.incrementPC();
        Pair<Boolean, ? extends LLVMAbstractState> check;
        switch (this.typeOfConversion) {
            case BITCAST:
                if (fromType.isAggregateType() || toType.isAggregateType()) {
                    throw new UndefinedBehaviorException("Only first class types are supported by a BITCAST", nodeNumber);
                }
                if (fromType.isPointerType() != toType.isPointerType()) {
                    throw new UndefinedBehaviorException("Cannot BITCAST between pointer and non-pointer values", nodeNumber);
                }
                if (fromType.size() != toType.size()) {
                    throw new UndefinedBehaviorException("BITCAST instruction invoked with wrong arguments!", nodeNumber);
                }
                return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
            case PTRTOINT:
                if (fromType.size() > toType.size()) {
                    return LLVMConversionInstruction.havoc(res, varName, fromRef, toType, useBoundedIntegers, aborter);
                }
                return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
            case TRUNC:
                if (useBoundedIntegers) {
                    // check if the value fits into the new type
                    boolean unsigned =
                        state.getModule().getUnsignedBitvectorVariables().contains(this.getIdentifier().getName());
                    IntegerType toIntegerType = toType.getIntegerType(unsigned, useBoundedIntegers);
                    check =
                        res.checkRelation(
                            relationFactory.lessThanEquals(
                                termFactory.constant(toIntegerType.getLower().getConstant()),
                                fromRef
                            ),
                            aborter
                        );
                    res = check.y;
                    if (check.x) {
                        check =
                            res.checkRelation(
                                relationFactory.lessThanEquals(
                                    fromRef,
                                    termFactory.constant(toIntegerType.getUpper().getConstant())
                                ),
                                aborter
                            );
                        res = check.y;
                        if (check.x) {
                            return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
                        }
                    }
                }
                if (fromType.size() <= toType.size()) {
                    throw new UndefinedBehaviorException("Cannot TRUNCATE from a type to type that is larger or has equal size", nodeNumber);
                }
                return LLVMConversionInstruction.havoc(res, varName, fromRef, toType, useBoundedIntegers, aborter);
            case SEXT:
                if (fromType.size() >= toType.size()) {
                    throw new UndefinedBehaviorException("SEXT instruction invoked with wrong arguments!", nodeNumber);
                }
                if (fromType.isBooleanType()) {
                    // special case for extending boolean types: the result is either -1 or 0
                    if (Globals.useAssertions) {
                        assert (!toType.isBooleanType()) : "Extension to same type - this should not happen.";
                    }
                    check = res.checkRelation(relationFactory.equalTo(fromRef, termFactory.one()), aborter);
                    res = check.y;
                    if (check.x) {
                        final Set<LLVMRelation> change = new LinkedHashSet<LLVMRelation>();
                        res = res.assign(varName, termFactory.negone(), toType, change, aborter);
                        return
                            Collections.singleton(
                                new LLVMSymbolicEvaluationResult(res, change)
                            );
                    } else {
                        check = res.checkRelation(relationFactory.equalTo(fromRef, termFactory.zero()), aborter);
                        res = check.y;
                        if (check.x) {
                            return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
                        } else {
                            final Set<LLVMRelation> change = new LinkedHashSet<LLVMRelation>();
                            res = res.assign(varName, null, toType, change, aborter);
                            final LLVMSymbolicVariable newVar = res.getSymbolicVariableForProgramVariable(varName);
                            final LLVMRelation lower = relationFactory.lessThanEquals(termFactory.negone(), newVar);
                            final LLVMRelation upper = relationFactory.lessThanEquals(newVar, termFactory.zero());
                            change.add(lower);
                            change.add(upper);
                            return
                                Collections.singleton(
                                    new LLVMSymbolicEvaluationResult(res.addRelation(lower, aborter).addRelation(upper, aborter), change)
                                );
                        }
                    }
                } else {
                    // the value (in signed interpretation) remains unchanged, but the type changes
                    return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
                }
            case ZEXT:
                check = res.checkRelation(relationFactory.nonNegative(fromRef), aborter);
                res = check.y;
                if (check.x) {
                    return LLVMConversionInstruction.noChange(res, varName, fromRef, fromType, toType, aborter);
                }
                // TODO re-implement special cases for bounded integers
                return LLVMConversionInstruction.havoc(res, varName, fromRef, toType, useBoundedIntegers, aborter);
            case FPEXT:
                return LLVMConversionInstruction.havoc(res, varName, fromRef, toType, useBoundedIntegers, aborter);
            default:
                // TODO: implement this
                throw new UnsupportedOperationException("Not yet implemented.");
        }
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        final LLVMType toType = this.getIdentifier().getType();
        final LLVMType fromType = this.fromLiteral.getType();
        
        switch (this.typeOfConversion) {
            case BITCAST:
                return false;
            case PTRTOINT:
                if (fromType.size() > toType.size()) {
                    return true;
                } else {
                    return false;
                }
            case TRUNC:
                return true;
            case SEXT:
                return false;
            case ZEXT:
                return true;
            case FPEXT:
                return true;
            default:
                throw new UnsupportedOperationException("Not yet implemented.");
        }
    }
    
    /**
     * @return True iff this is a TRUNC instruction.
     */
    public boolean isTRUNC() {
        return (this.typeOfConversion == LLVMConvInstrType.TRUNC);
    }
    
    /**
     * @return True iff this is a ZEXT instruction.
     */
    public boolean isZEXT() {
        return (this.typeOfConversion == LLVMConvInstrType.ZEXT);
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = "));
        res.append(eu.tttext(this.typeOfConversion.toString().toLowerCase()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.fromLiteral.getType().toString()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.fromLiteral.toString()));
        res.append(eu.tttext(" to "));
        res.append(eu.tttext(this.getIdentifier().getType().toString()));
        return res.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // I don't really get it, so I'll just consider all variables
        // in this instruction interesting
        this.collectVariables(vars);
        return vars;
    }
    
    /**
     * @return The set of names of operands of this instruction.
     */
    public String getOperandName() {
        if (this.fromLiteral instanceof LLVMVariableLiteral) {
            return ((LLVMVariableLiteral)this.fromLiteral).getName();
        }
        return null;
    }

    /**
     * @return The set of operands of this instruction.
     */
    public LLVMLiteral getOperand() {
        return this.fromLiteral;
    }
    
    /**
     * @return True iff this seems like an instruction on originally signed integers.
     */
    public boolean seemsSigned() {
        return (this.typeOfConversion == LLVMConvInstrType.SEXT);
    }
    
    /**
     * @return True iff this seems like an instruction on originally unsigned integers.
     */
    public boolean seemsUnsigned() {
        return (this.typeOfConversion == LLVMConvInstrType.ZEXT);
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("ConversionInstr ");
        strBuilder.append(" operator: " + this.typeOfConversion);
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" fromType: " + this.fromLiteral.getType());
        strBuilder.append(" fromLiteral: " + this.fromLiteral);
        strBuilder.append(" toType: " + this.getIdentifier().getType());
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toDOTString());
        res.append(" = ");
        res.append(this.typeOfConversion.toString().toLowerCase());
        res.append(" ");
        res.append(this.fromLiteral.getType());
        res.append(" ");
        res.append(this.fromLiteral.toDOTString());
        res.append(" to ");
        res.append(this.getIdentifier().getType());
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = ");
        res.append(this.typeOfConversion.toString().toLowerCase());
        res.append(" ");
        res.append(this.fromLiteral.getType());
        res.append(" ");
        res.append(this.fromLiteral);
        res.append(" to ");
        res.append(this.getIdentifier().getType());
        return res.toString();
    }
}
