package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMFCmpInstruction extends LLVMAssignmentInstruction {

    /**
     * The type of the comparison.
     */
    private final LLVMFloatCmpOpType comparisonCode;

    /**
     * The first operand (type must be float or vector of floats).
     */
    private final LLVMLiteral operand1Value;

    /**
     * The second operand (type must be float or vector of floats).
     */
    private final LLVMLiteral operand2Value;

    /**
     * @param id The variable to assign the comparison result to.
     * @param cmpCode The type of the comparison.
     * @param op1 The first operand (type must be float or vector of floats).
     * @param op2 The second operand (type must be float or vector of floats).
     * @param debugLine The index of the line with debug information.
     */
    public LLVMFCmpInstruction(LLVMVariableLiteral id, LLVMFloatCmpOpType cmpCode, LLVMLiteral op1, LLVMLiteral op2, int debugLine) {
        super(id, debugLine);
        if (Globals.useAssertions && op1 != null && op2 != null) {
            assert (op1.getType().equals(op2.getType())) : "Both operands must have the same type!";
        }
        this.comparisonCode = cmpCode;
        this.operand1Value = op1;
        this.operand2Value = op2;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.operand1Value);
        LLVMInstruction.collectVariable(vars, this.operand2Value);
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
        // TODO
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter) {
        Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
        res.addAll(trueResult(state, aborter));
        res.addAll(falseResult(state, aborter));
        return res;
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String export(Export_Util eu) {
        return this.toString();
    }

    /**
     * @return The type of the comparison.
     */
    public LLVMFloatCmpOpType getComparisonCode() {
        return this.comparisonCode;
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return The first operand.
     */
    public LLVMLiteral getOperand1Value() {
        return this.operand1Value;
    }

    /**
     * @return The second operand.
     */
    public LLVMLiteral getOperand2Value() {
        return this.operand2Value;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("FloatCmpInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" cmp: " + this.comparisonCode);
        strBuilder.append(" op1Value: " + this.operand1Value);
        strBuilder.append(" op2Value: " + this.operand2Value);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toDOTString());
        res.append(" = fcmp ");
        res.append(this.comparisonCode);
        res.append(" ");
        if (this.operand1Value != null) {
            res.append(this.operand1Value.toDOTString());
        }
        res.append(this.operand1Value.toDOTString());
        res.append(" ");
        if (this.operand2Value != null) {
            res.append(this.operand2Value.toDOTString());
        }
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = fcmp ");
        res.append(this.comparisonCode);
        res.append(" ");
        res.append(this.operand1Value);
        res.append(" ");
        res.append(this.operand2Value);
        return res.toString();
    }
    
    /**
     * @param state The base state.
     * @return An abstract state emerging from the base state by setting the result variable for the comparison to
     *         false and incrementing the PC.
     */
    private Set<LLVMSymbolicEvaluationResult> falseResult(LLVMAbstractState state, Abortion aborter) {
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        LLVMAbstractState newState = state.assign(
                                                  this.getIdentifier().getName(),
                                                  state.getRelationFactory().getTermFactory().zero(),
                                                  LLVMIntType.I1,
                                                  newRels,
                                                  aborter
                );
        newState = newState.incrementPC();
        return Collections.singleton(new LLVMSymbolicEvaluationResult(newState, newRels));
    }

    /**
     * @param state The base state.
     * @return An abstract state emerging from the base state by setting the result variable for the comparison to
     *         true and incrementing the PC.
     */
    private Set<LLVMSymbolicEvaluationResult> trueResult(LLVMAbstractState state, Abortion aborter) {
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        LLVMAbstractState newState = state.assign(
                                                  this.getIdentifier().getName(),
                                                  state.getRelationFactory().getTermFactory().one(),
                                                  LLVMIntType.I1,
                                                  newRels,
                                                  aborter
                );
        newState = newState.incrementPC();

        return Collections.singleton(new LLVMSymbolicEvaluationResult(newState, newRels));
    }

}
