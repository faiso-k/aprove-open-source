package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Janine Repke, CryingShadow
 * TODO documentation
 */
public class LLVMVaArgInstruction extends LLVMAssignmentInstruction {

    // TODO document me
    private final LLVMLiteral varArgList;

    /**
     * @param id The variable to assign the result to.
     * @param vaList TODO document me
     * @param debugLine The index of the line with debug information.
     */
    public LLVMVaArgInstruction(LLVMVariableLiteral id, LLVMLiteral vaList, int debugLine) {
        super(id, debugLine);
        this.varArgList = vaList;
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.varArgList);
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
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not yet implemented.");
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = va_arg");
        res.append(this.varArgList);
        res.append(", ");
        res.append(this.getArgumentType());
        return res.toString();
    }

    /**
     * @return TODO document me
     */
    public LLVMType getArgumentType() {
        return this.getIdentifier().getType();
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return TODO document me
     */
    public LLVMLiteral getVarArgValue() {
        return this.varArgList;
    }

    @Override
    public String toDebugString() {
        // TODO this is just wrong
        StringBuilder strBuilder = new StringBuilder("ShuffleVectorExpr ");
        strBuilder.append(" vaArgType: " + this.varArgList.getType());
        strBuilder.append(" vaArgValue: " + this.varArgList);
        strBuilder.append(" argumentType: " + this.getArgumentType());
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        // TODO this is just wrong
        StringBuilder strBuilder = new StringBuilder("ShuffleVectorExpr ");
        strBuilder.append(" vaArgType: " + this.varArgList.getType());
        strBuilder.append(" vaArgValue: " + this.varArgList.toDOTString());
        strBuilder.append(" argumentType: " + this.getArgumentType());
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        return this.getIdentifier() + " = va_arg" + this.varArgList + ", " + this.getArgumentType();
    }

}
