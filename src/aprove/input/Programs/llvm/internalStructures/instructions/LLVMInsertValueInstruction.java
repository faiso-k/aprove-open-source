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
public class LLVMInsertValueInstruction extends LLVMAssignmentInstruction {

    /**
     * The aggregate in which to insert the element.
     */
    private final LLVMLiteral aggregateLiteral;

    /**
     * The element to insert.
     */
    private final LLVMLiteral elementLiteral;

    /**
     * The indices where to insert the element.
     */
    private final ImmutableList<LLVMLiteral> indices;

    /**
     * @param id The variable to assign the resulting aggregate to.
     * @param elem The element to insert.
     * @param idxs The indices where to insert the element.
     * @param aggr The aggregate in which to insert the element.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMInsertValueInstruction(
        LLVMVariableLiteral id,
        LLVMLiteral elem,
        ImmutableList<LLVMLiteral> idxs,
        LLVMLiteral aggr,
        int debugLine
    ) {
        super(id, debugLine);
        this.elementLiteral = elem;
        this.indices = idxs;
        this.aggregateLiteral = aggr;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.aggregateLiteral);
        LLVMInstruction.collectVariable(vars, this.elementLiteral);
        for (LLVMLiteral ind : this.indices) {
            LLVMInstruction.collectVariable(vars, ind);
        }
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
     * @return The aggregate in which to insert the element.
     */
    public LLVMLiteral getAggregateLiteral() {
        return this.aggregateLiteral;
    }

    /**
     * @return The element to insert.
     */
    public LLVMLiteral getElementLiteral() {
        return this.elementLiteral;
    }

    /**
     * @return The indices where to insert the element.
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
        StringBuilder strBuilder = new StringBuilder("InsertValueInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" aggrLiteral: " + this.aggregateLiteral);
        strBuilder.append(" elementLiteral: " + this.elementLiteral);
        strBuilder.append(" indices: (");
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
            new StringBuilder("insertvalue "
                + this.aggregateLiteral.toDOTString()
                + ", "
                + this.elementLiteral.toDOTString());
        boolean first = true;
        for (LLVMLiteral index : this.indices) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(index.toDOTString());
        }
        return strBuilder.toString();

    }

    @Override
    public String toString() {
        StringBuilder strBuilder =
            new StringBuilder("insertvalue " + this.aggregateLiteral + ", " + this.elementLiteral);
        boolean first = true;
        for (LLVMLiteral index : this.indices) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(index);
        }
        return strBuilder.toString();
    }

}
