package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
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
public class LLVMIndirectBrInstruction extends LLVMBranchInstruction {

    /**
     * The address.
     */
    private final LLVMLiteral addressLit;

    /**
     * The jumping labels.
     */
    private final ImmutableList<String> labels;

    /**
     * @param addr The address.
     * @param labelsParam The jumping labels.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMIndirectBrInstruction(LLVMLiteral addr, ImmutableList<String> labelsParam, int debugLine) {
        super(debugLine);
        this.addressLit = addr;
        this.labels = labelsParam;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        LLVMInstruction.collectVariable(coneVars, this.addressLit);
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.addressLit);
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
     * @return The address.
     */
    public LLVMLiteral getAddressLit() {
        return this.addressLit;
    }

    @Override
    public Set<String> getInterestingVariables() {
        // TODO implement this along with refine()
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /**
     * @return The jumping labels.
     */
    public ImmutableList<String> getLabels() {
        return this.labels;
    }

    @Override
    public String getProducedVariable() {
        return null;
    }

    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        List<LLVMProgramPosition> poss = new ArrayList<LLVMProgramPosition>();
        for (String label : this.labels) {
            poss.add(new LLVMProgramPosition(pos.x, label, 0));
        }
        return poss;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("IndirectBrInstr ");
        strBuilder.append(" AddrLit: " + this.addressLit);
        strBuilder.append(" Labels: (");
        boolean first = true;
        for (String label : this.labels) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + label);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder = new StringBuilder("indirectbr " + this.addressLit.toDOTString() + "[");
        this.toString(strBuilder);
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("indirectbr " + this.addressLit + "[");
        this.toString(strBuilder);
        return strBuilder.toString();
    }

    /**
     * @param strBuilder The StringBuilder to construct the String representation for this object with.
     */
    private void toString(StringBuilder strBuilder) {
        boolean first = true;
        for (String label : this.labels) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append("%" + label);
        }
        strBuilder.append("]");
    }

}
