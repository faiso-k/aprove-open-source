package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.*;
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
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The alloca instruction for allocating memory on the current function stack frame.
 * @author Janine Repke, cryingshadow
 */
public class LLVMAllocaInstruction extends LLVMAssignmentInstruction {

    /**
     * @param state The state.
     * @param newRef The symbolic variable.
     * @param type The type of the symbolic variable.
     * @param offset An offset on the number of bytes that the specified symbolic variable is away from its bound.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The specified state where an upper bound on the value of the specified symbolic variable is added in
     *         case that bounded integers are used. The bound is determined by the specified type and offset.
     *         Otherwise, just the specified state is returned without any change.
     */
    public static LLVMAbstractState upperBound(
        LLVMAbstractState state,
        LLVMSymbolicVariable newRef,
        LLVMPointerType type,
        BigInteger offset,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        if (state.getStrategyParamters().useBoundedIntegers) {
            LLVMRelation rel = state.getRelationFactory().lessThanEquals(
                                    newRef,
                                    state.getRelationFactory().getTermFactory().constant(
                                        type.getIntegerType(true, true).getUpper().getConstant().subtract(offset)
                                    )
                                );
            if (newRels != null) {
                newRels.add(rel);
            }
            return state.addRelation(rel, aborter);
        }
        return state;
    }

    /**
     * @param typeSize The size of the type to compute an offset for.
     * @param factor The factor to multiply the type size.
     * @return The computed offset.
     */
    private static BigInteger computeOffset(BigInteger typeSize, BigInteger factor) {
        return typeSize.multiply(factor).subtract(BigInteger.ONE);
    }

    /**
     * Optional constant alignment as a lower boundary.
     */
    private final LLVMLiteral alignment;

    /**
     * The type of the allocated element(s).
     */
    private final LLVMType generalType;

    /**
     * The number of elements allocated.
     */
    private final LLVMLiteral numElementsLit;

    /**
     * @param id The name of the assigned variable.
     * @param type The type of the allocated element(s).
     * @param num The number of elements allocated.
     * @param align Optional constant alignment.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMAllocaInstruction(
        LLVMVariableLiteral id,
        LLVMType type,
        LLVMLiteral num,
        LLVMLiteral align,
        int debugLine
    ) {
        super(id, debugLine);
        this.generalType = type;
        this.numElementsLit = num;
        this.alignment = align;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.numElementsLit);
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        return null;
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        // allocations do not change conditions
        return conditions;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        final LLVMModule module = state.getModule();
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        
        // determine the new variable
        LLVMPointerType type = new LLVMPointerType(this.generalType, module.getPointerSize(), null);
        LLVMSymbolicVariable newRef = termFactory.freshVariable();
        
        LLVMRelation positiveRel = relationFactory.positive(newRef);
        LLVMAbstractState newState = state.addRelation(positiveRel, aborter);
        newRels.add(positiveRel);
        
        LLVMType targetType = type.getTargetType();
        BigInteger typeSize = BigInteger.valueOf(IntegerUtils.bitsToBytes(targetType.size()));
        // offset for allocated memory in bytes
        BigInteger offset;
        if (this.numElementsLit == null) {
            offset = typeSize.subtract(BigInteger.ONE);
        } else if (this.numElementsLit instanceof LLVMIntLiteral) {
            offset =
                LLVMAllocaInstruction.computeOffset(
                    typeSize,
                    ((LLVMIntLiteral)this.numElementsLit).getValueAsBigInteger()
                );

        } else if (
            this.numElementsLit instanceof LLVMVariableLiteral && 
                state.getSimpleTermForLiteral(this.numElementsLit) instanceof LLVMConstant) {
            offset =
                LLVMAllocaInstruction.computeOffset(
                    typeSize,
                    ((LLVMConstant)state.getSimpleTermForLiteral(this.numElementsLit)).getIntegerValue()
                );
        } else {
            offset = null;
        }
        
        if (offset == null) {
            // we possibly have a variable size allocation
            LLVMSimpleTerm numRef = newState.getSimpleTermForLiteral(this.numElementsLit);
            if (numRef instanceof LLVMSymbolicVariable) {
                LLVMSymbolicVariable numVar = (LLVMSymbolicVariable)numRef;
                if (newState.isPossiblyTrapValue(numVar)) {
                    throw new TrapValueException(nodeNumber);
                }
                final Pair<Boolean, ? extends LLVMAbstractState> check =
                    newState.checkRelation(relationFactory.positive(numVar), aborter);
                newState = check.y;
                if (proveMemorySafety && !check.x) {
                    throw new UndefinedBehaviorException(
                        "Allocation parameter might be zero or negative at node " + nodeNumber + "!"
                    );
                }
                // we really have a variable size allocation
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                newState = newState.applyArrayPatternHeuristicForAllocation(
                                newRef,
                                numVar,
                                limitRef
                            );
                
                LLVMRelation rel = relationFactory.equalTo(
                                        termFactory.operation(
                                            ArithmeticOperationType.ADD,
                                            newRef,
                                            termFactory.operation(
                                                ArithmeticOperationType.MUL,
                                                termFactory.constant(typeSize),
                                                numRef
                                            )
                                        ),
                                        termFactory.operation(
                                            ArithmeticOperationType.ADD,
                                            termFactory.one(),
                                            limitRef
                                        )
                                    );
                newState = newState.addRelation(rel, aborter);
                newRels.add(rel);
                
                newState = newState.allocateMemoryAndAssociatePointer(
                                newRef,
                                limitRef,
                                newRef,
                                type,
                                true,
                                newRels,
                                aborter
                            );
            } else if (numRef instanceof LLVMConstant) {
                BigInteger constant = ((LLVMConstant)numRef).getIntegerValue();
                if (constant.compareTo(BigInteger.ZERO) <= 0) {
                    throw new UndefinedBehaviorException(
                        "Allocation parameter is zero or negative at node " + nodeNumber + "!"
                    );
                }
                offset = LLVMAllocaInstruction.computeOffset(typeSize, constant);
                if (offset.compareTo(BigInteger.ZERO) == 0) {
                    // only one memory cell
                    newState = newState.allocateMemoryAndAssociatePointer(newRef, newRef, newRef, type, true, newRels, aborter);
                } else if (offset.compareTo(BigInteger.ZERO) < 0) {
                    throw new UndefinedBehaviorException(
                        "Allocation of zero or a negative number of bytes at node " + nodeNumber + "!"
                    );
                } else {
                    newState = LLVMAllocaInstruction.upperBound(newState, newRef, type, offset, newRels, aborter);
                    LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                    
                    LLVMRelation rel = relationFactory.createAdditionRelation(limitRef, newRef, termFactory.constant(offset));
                    newState = newState.addRelation(rel, aborter);
                    newRels.add(rel);
                    
                    newState = newState.allocateMemoryAndAssociatePointer(
                                    newRef,
                                    limitRef,
                                    newRef,
                                    type,
                                    true,
                                    newRels,
                                    aborter
                                );
                }
            } else {
                throw new IllegalStateException(
                    "A literal yielded a return value different from a variable or constant!"
                );
            }
        } else {
            if (offset.compareTo(BigInteger.ZERO) == 0) {
                // only one memory cell
                newState = newState.allocateMemoryAndAssociatePointer(newRef, newRef, newRef, type, true, newRels, aborter);
                newState = LLVMAllocaInstruction.upperBound(newState, newRef, type, offset, newRels, aborter);
            } else if (offset.compareTo(BigInteger.ZERO) < 0) {
                throw new UndefinedBehaviorException(
                    "Allocation of zero or a negative number of bytes at node " + nodeNumber + "!"
                );
            } else {
                newState = LLVMAllocaInstruction.upperBound(newState, newRef, type, offset, newRels, aborter);
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                
                LLVMRelation rel = relationFactory.createAdditionRelation(
                                      limitRef,
                                      newRef,
                                      termFactory.constant(offset)
                                  );
                //if (!newState.getStrategyParamters().useOptimizations || !this.generalType.isIntType()) {
                if (!this.generalType.isIntType() || state.getModule().getAllPositions().size() < Globals.INSTRUCTION_COUNT_THRESHOLD) {
                    newState = newState.addRelation(rel, aborter);
                    newRels.add(rel);
                }
                newState = newState.allocateMemoryAndAssociatePointer(
                        newRef,
                        limitRef,
                        newRef,
                        type,
                        true,
                        newRels,
                        aborter
                    );
            }
        }
        // create modulo relation for alignment
        if (!state.getStrategyParamters().useOptimizations) {
            int align = 0;
            if (this.alignment == null) {
                align = module.getAbiAlignment(this.generalType);
            } else {
                align = this.alignment.toInt();
            }
            if (this.generalType.equals(LLVMIntType.I8) && this.numElementsLit != null) {
                if (this.numElementsLit instanceof LLVMIntLiteral) {
                    int size = this.numElementsLit.toInt();
                    if (size >= 4 && align < 4) {
                        align = 4;
                    }
                } else if (this.numElementsLit instanceof LLVMVariableLiteral) {
                    LLVMSymbolicVariable sym =
                        newState.getSymbolicVariableForProgramVariable(this.numElementsLit.getName());
                    final Pair<Boolean, ? extends LLVMAbstractState> check =
                        newState.checkRelation(sym, IntegerRelationType.GE, termFactory.constant(4), aborter);
                    newState = check.y;
                    if (check.x) {
                        align = 4;
                    }
                }
            }
            if (align > 1) {
                if (Globals.useAssertions) {
                    // clang requires this; llvm specification seems not to be specific about it.
                    assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
                }
                
                LLVMRelation alignmentRel = relationFactory.createAlignmentRelation(newRef, termFactory.constant(BigInteger.valueOf(align)));
                newState = newState.addRelation(alignmentRel, aborter);
                newRels.add(alignmentRel);
            }
        }
        // set entry in variable function, increment program counter, and unset refinement flag
        newState = newState.setProgramVariable(this.getIdentifier().getName(), newRef, type).incrementPC();
        LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(newState, newRels);
        return Collections.singleton(evaluationResult);
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = alloca "));
        res.append(eu.tttext(this.generalType.toString()));
        if (this.numElementsLit != null) {
            res.append(eu.tttext(", "));
            res.append(eu.tttext(this.numElementsLit.toString()));
        }
        if (this.alignment != null) {
            res.append(eu.tttext(", align "));
            res.append(eu.tttext(this.alignment.toString()));
        }
        return res.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("AllocaInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" generalType: " + this.generalType);
        strBuilder.append(" numElementsType: " + this.numElementsLit.getType());
        strBuilder.append(" numElementsLit: " + this.numElementsLit);
        if (this.alignment != null) {
            strBuilder.append("alignment: " + this.alignment);
        }
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder =
            new StringBuilder(this.getIdentifier().toDOTString() + " = alloca " + this.generalType);
        if (this.numElementsLit != null) {
            strBuilder.append(", " + this.numElementsLit.toDOTString());
        }
        if (this.alignment != null) {
            strBuilder.append(", align " + this.alignment);
        }
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder(this.getIdentifier() + " = alloca " + this.generalType);
        if (this.numElementsLit != null) {
            strBuilder.append(", numElementsLit: " + this.numElementsLit);
        }
        if (this.alignment != null) {
            strBuilder.append(", align " + this.alignment);
        }
        return strBuilder.toString();
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }
}

