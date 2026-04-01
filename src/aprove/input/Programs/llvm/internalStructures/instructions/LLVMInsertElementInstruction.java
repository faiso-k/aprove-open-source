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
public class LLVMInsertElementInstruction extends LLVMAssignmentInstruction {

    /**
     * The element to insert.
     */
    private final LLVMLiteral elementLiteral;

    /**
     * The index where to insert the element.
     */
    private final LLVMLiteral indexLiteral;

    /**
     * The vector in which to insert the element.
     */
    private final LLVMLiteral vectorLiteral;

    /**
     * @param id the variable to assign the resulting vector to.
     * @param elem The element to insert.
     * @param idx The index where to insert the element.
     * @param vec The vector in which to insert the element.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMInsertElementInstruction(LLVMVariableLiteral id, LLVMLiteral elem, LLVMLiteral idx, LLVMLiteral vec, int debugLine) {
        super(id, debugLine);
        this.elementLiteral = elem;
        this.indexLiteral = idx;
        this.vectorLiteral = vec;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.indexLiteral);
        LLVMInstruction.collectVariable(vars, this.elementLiteral);
        LLVMInstruction.collectVariable(vars, this.vectorLiteral);
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
     * @return The element to insert.
     */
    public LLVMLiteral getElementLiteral() {
        return this.elementLiteral;
    }

    /**
     * @return The index where to insert the element.
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
     * @return The vector in which to insert the element.
     */
    public LLVMLiteral getVectorLiteral() {
        return this.vectorLiteral;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("InsertElementInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" vectorLiteral: " + this.vectorLiteral);
        strBuilder.append(" elementLiteral: " + this.elementLiteral);
        strBuilder.append(" indexLiteral: " + this.indexLiteral);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        // TODO: correct order of vectorLit and elementLit?
        return new String(this.getIdentifier().toDOTString()
            + " = insertelement "
            + this.vectorLiteral.toDOTString()
            + ", "
            + this.elementLiteral.toDOTString());
    }

    @Override
    public String toString() {
        // TODO: correct order of vectorLit and elementLit?
        return new String(this.getIdentifier() + " = insertelement " + this.vectorLiteral + ", " + this.elementLiteral);
    }

}
