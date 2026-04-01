package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.input.Programs.llvm.exceptions.*;
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

/**
 * LLVMDoc: The 'unreachable' instruction has no defined semantics.
 * @author Janine Repke, CryingShadow
 */
public class LLVMUnreachableInstruction extends LLVMTerminatorInstruction {
    
    public LLVMUnreachableInstruction() {
        super(-1);
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
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        throw new UndefinedBehaviorException("Executed unreachable instruction at node " + nodeNumber + ".");
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        return this.toString();
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
        return Collections.emptyList();
    }

    @Override
    public String toDebugString() {
        String str = "Unreachable Instr ";
        return str;
    }

    @Override
    public String toDOTString() {
        return this.toString();
    }

    @Override
    public String toString() {
        return new String("unreachable");
    }

}
