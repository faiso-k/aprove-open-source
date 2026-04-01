package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
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
 */
public class LLVMExtractElementInstruction extends LLVMAssignmentInstruction {

    /**
     * The index of the element to extract (must be of type i32).
     */
    private final LLVMLiteral indexLiteral;

    /**
     * The vector to extract the element from.
     */
    private final LLVMLiteral vectorLiteral;

    /**
     * @param id The variable to assign the extracted element to.
     * @param indexLit The index of the element to extract.
     * @param vecLit The vector to extract the element from.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMExtractElementInstruction(LLVMVariableLiteral id, LLVMLiteral indexLit, LLVMLiteral vecLit, int debugLine) {
        super(id, debugLine);
        this.indexLiteral = indexLit;
        this.vectorLiteral = vecLit;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.indexLiteral);
        LLVMInstruction.collectVariable(vars, this.vectorLiteral);
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
        return this.toString();
    }

    /**
     * @return The index of the element to extract.
     */
    public LLVMLiteral getIndexLiteral() {
        return this.indexLiteral;
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return The vector to extract the element from.
     */
    public LLVMLiteral getVectorLiteral() {
        return this.vectorLiteral;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("ExtactElemntInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" vectorLiteral: " + this.vectorLiteral);
        strBuilder.append(" indexLiteral: " + this.indexLiteral);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        return new String(this.getIdentifier().toDOTString()
            + " = extractelement "
            + this.vectorLiteral.toDOTString()
            + ", "
            + this.indexLiteral.toDOTString());
    }

    @Override
    public String toString() {
        return new String(this.getIdentifier() + " = extractelement " + this.vectorLiteral + ", " + this.indexLiteral);
    }

}
