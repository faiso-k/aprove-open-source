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
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 */
public class LLVMExtractValueInstruction extends LLVMAssignmentInstruction {

    /**
     * The aggregate (array or struct) to extract a value from.
     */
    private final LLVMLiteral aggregateLiteral;

    /**
     * The indices accessing the value in the aggregate.
     */
    private final ImmutableList<LLVMLiteral> indices;

    /**
     * @param id The variable to assign the extracted value to.
     * @param aggregate The aggregate to extract a value from.
     * @param idxs The indices accessing the value in the aggregate.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMExtractValueInstruction(LLVMVariableLiteral id, LLVMLiteral aggregate, ImmutableList<LLVMLiteral> idxs, int debugLine) {
        super(id, debugLine);
        this.aggregateLiteral = aggregate;
        this.indices = idxs;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.aggregateLiteral);
        for (LLVMLiteral ind : this.indices) {
            LLVMInstruction.collectVariable(vars, ind);
        }
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
     * @return The aggregate (array or struct) to extract a value from.
     */
    public LLVMLiteral getAggregateLiteral() {
        return this.aggregateLiteral;
    }

    /**
     * @return The indices accessing the value in the aggregate.
     */
    public ImmutableList<LLVMLiteral> getIndices() {
        return this.indices;
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("ExtactValueInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" aggrLiteral: " + this.aggregateLiteral);
        strBuilder.append(" indexes: (");
        boolean first = true;
        for (LLVMLiteral index : this.indices) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + index);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder =
            new StringBuilder(this.getIdentifier().toDOTString()
                + " = extractvalue "
                + this.aggregateLiteral.toDOTString());
        for (LLVMLiteral index : this.indices) {
            strBuilder.append(", " + index.toDOTString());
        }
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        StringBuilder strBuilder =
            new StringBuilder(this.getIdentifier() + " = extractvalue " + this.aggregateLiteral);
        for (LLVMLiteral index : this.indices) {
            strBuilder.append(", " + index);
        }
        return strBuilder.toString();
    }

}
