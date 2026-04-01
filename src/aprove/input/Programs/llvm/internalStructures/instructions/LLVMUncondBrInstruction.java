package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
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
 * An unconditional branch instruction.
 * @author Janine Repke, CryingShadow
 */
public class LLVMUncondBrInstruction extends LLVMBranchInstruction {

    /**
     * The branch address for an unconditional branch.
     */
    private final String branchLabel;

    /**
     * @param label The label to branch to.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMUncondBrInstruction(String label, int debugLine) {
        super(debugLine);
        this.branchLabel = label;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        // there are no cone variables
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        // do nothing
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
        for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            if (pair.y.contains(pos.y)) {
                // do not follow loops
                continue;
            }
            List<String> path = new ArrayList<String>(pair.y);
            path.add(pos.y);
            res.add(new Pair<IntegerRelationSet, List<String>>(pair.x, path));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        LLVMAbstractState newState = state.branchToBlock(this.branchLabel, nodeNumber, newRels, aborter);
        
        LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(newState, newRels);
        return Collections.singleton(evaluationResult);
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext("br %"));
        res.append(eu.tttext(this.branchLabel));
        return res.toString();
    }

    /**
     * @return The name of the label to branch to.
     */
    public String getBranchLabel() {
        return this.branchLabel;
    }

    @Override
    public Set<String> getInterestingVariables() {
        return Collections.emptySet();
    }

    @Override
    public String getProducedVariable() {
        return null;
    }

    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        return Collections.singletonList(new LLVMProgramPosition(pos.x, this.branchLabel, 0));
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("UncondBrInstr ");
        strBuilder.append(" branchLabel: " + this.branchLabel);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        return this.toString();
    }

    @Override
    public String toString() {
        return new String("br %" + this.branchLabel);
    }

}
