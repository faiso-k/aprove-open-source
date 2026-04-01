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
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Load a value from memory.
 * @author Janine Repke, CryingShadow
 */
public class LLVMLoadInstruction extends LLVMAssignmentInstruction {

    /**
     * The alignment for the load.
     */
    private final LLVMLiteral alignment;

    /**
     * The literal describing the pointer from which to load.
     */
    private final LLVMLiteral pointerLiteral;

    /**
     * @param id The variable to assign the loaded value to.
     * @param pointerLit The literal describing the pointer from which to load.
     * @param align The alignment for the load.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMLoadInstruction(LLVMVariableLiteral id, LLVMLiteral pointerLit, LLVMLiteral align, int debugLine) {
        super(id, debugLine);
        this.pointerLiteral = pointerLit;
        this.alignment = align;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        LLVMInstruction.collectVariable(coneVars, this.pointerLiteral);
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.pointerLiteral);
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
        Set<Pair<IntegerRelationSet, List<String>>> res = new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
        String name = this.getIdentifier().getName();
        LLVMHeuristicProgVarRef oldVariable = new LLVMHeuristicProgVarRef(name, name);
        if (!(this.pointerLiteral instanceof LLVMVariableLiteral)) {
            // we cannot infer conditions - the set is empty
            return res;
        }
        String otherName = ((LLVMVariableLiteral)this.pointerLiteral).getName();
        LLVMHeapVarRef newNode = new LLVMHeapVarRef(otherName, otherName);
        for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            IntegerRelationSet relSet = new IntegerRelationSet();
            for (IntegerRelation rel : pair.x) {
                relSet.add(rel.applySubstitution(oldVariable, newNode));
            }
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, pair.y));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException, MemorySafetyException {
        final LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.pointerLiteral);
        final LLVMPointerType type = this.pointerLiteral.getType().getThisAsPointerType();
        final LLVMType targetType = type.getTargetType();
        final Pair<LLVMAssociationIndex, LLVMAbstractState> allocationIndex =
            state.getAssociatedAllocationIndex(pointerRef, type, false, aborter);
        LLVMAbstractState newState = allocationIndex.y;
        boolean unsigned;
        if (newState.getStrategyParamters().useBoundedIntegers) {
            unsigned = newState.getModule().getUnsignedBitvectorVariables().contains(this.getIdentifier().getName());
        } else {
            unsigned = newState.getModule().getUnsignedUnboundedVariables().contains(this.getIdentifier().getName());
        }
        if (newState.isPossiblyTrapValue(pointerRef)) {
            throw new TrapValueException(nodeNumber);
        }
        boolean isStructPointer = false;
        if (pointerRef instanceof LLVMSymbolicVariable) {
            isStructPointer = state.isStructPointer((LLVMSymbolicVariable)pointerRef);
        }
        if (proveMemorySafety && allocationIndex.x == null && !isStructPointer) {
            throw new MemorySafetyException(nodeNumber);
        }
//        LLVMSimpleTerm startAddress = newState.getAllocations().get(allocationIndex.x.x).x;
//        if (newState.getStrategyParamters().proveMemorySafety
//            && newState.getDereferencedAccessSimple(pointerRef, targetType, unsigned) == null
//            && newState.getDereferencedAccessSimple(startAddress, targetType, unsigned) == null){
//            throw new MemorySafetyException(nodeNumber);
//        }
        // check alignment
        if (!newState.getStrategyParamters().useOptimizations && this.alignment != null) {
            int align = this.alignment.toInt();
            if (Globals.useAssertions) {
                // clang requires this; llvm specification seems not to be specific about it.
                assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
            }
            if (proveMemorySafety && align > 1) {
                final Pair<Boolean, ? extends LLVMAbstractState> check =
                    newState.checkRelation(
                        newState.getRelationFactory().createAlignmentRelation(
                            pointerRef,
                            newState.getRelationFactory().getTermFactory().constant(BigInteger.valueOf(align))
                        ),
                        aborter
                    );
                newState = check.y;
                if (!check.x) {
//                    throw new UndefinedBehaviorException("Wrong alignment at node " + nodeNumber + ".");
                }
            }
        }
        
        
        // determine the pointed to value in the heap
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        
        LLVMSimpleTerm pointedToRef = newState.getDereferencedAccessSimple(pointerRef, targetType, unsigned, aborter);
        final String varName = this.getIdentifier().getName();
        newState = newState.incrementPC().assign(varName, pointedToRef, targetType, newRels, aborter);
        if (pointedToRef == null) {
            // if there was no pointed value in the memory, it is set now
            newState =
                newState.setSimpleHeapEntry(
                    pointerRef,
                    targetType,
                    unsigned,
                    newState.getSymbolicVariableForProgramVariable(varName),
                    aborter
                );
        }
        return Collections.singleton(new LLVMSymbolicEvaluationResult(newState, newRels));
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        final LLVMSimpleTerm pointerRef = state.getSimpleTermForLiteral(this.pointerLiteral);
        final LLVMPointerType type = this.pointerLiteral.getType().getThisAsPointerType();
        boolean unsigned;
        if (state.getStrategyParamters().useBoundedIntegers) {
            unsigned = state.getModule().getUnsignedBitvectorVariables().contains(this.getIdentifier().getName());
        } else {
            unsigned = state.getModule().getUnsignedUnboundedVariables().contains(this.getIdentifier().getName());
        }
        final LLVMSimpleTerm pointedToRef =
            state.getDereferencedAccessSimple(pointerRef, type.getTargetType(), unsigned, aborter);
        // Check if there is a pointee value saved in the state. If this is the case, load simply dereferences
        // the value and the operation is no over-approximation. Otherwise a new value is assigned and the 
        // evaluation is an over-approximation
        if (pointedToRef != null) {
            return false;
        } else {
            return true;
        }
    }

    @Override
    public String export(Export_Util eu) {
        return eu.tttext(this.getIdentifier().toString() + " = load " + this.pointerLiteral.toString());
    }

    /**
     * @return The pointer literal for the address to load from.
     */
    public LLVMLiteral getAddressValue() {
        return this.pointerLiteral;
    }

    /**
     * @return The alignment literal.
     */
    public LLVMLiteral getAlignment() {
        return this.alignment;
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("LoadInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" pointerType: " + this.pointerLiteral.getType());
        strBuilder.append(" pointerLiteral: " + this.pointerLiteral);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        return this.getIdentifier().toDOTString() + " = load " + this.pointerLiteral.toDOTString();
    }

    @Override
    public String toString() {
        return this.getIdentifier() + " = load " + this.pointerLiteral;
    }

}
