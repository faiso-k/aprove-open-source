package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.Graph.*;


//should be compared via object ID
public class LLVMIntersectionResult {




	public LLVMIntersectionResult(LLVMIntersector intersector, Node<LLVMAbstractState> intersectionNode, LLVMIntersectionResult identicalPreviousResult, LLVMIntermediateIntersectionResult legacyResult) {
		this.intersector = intersector;
		this.intersectionNode = intersectionNode;
		this.legacyResult = legacyResult;
		this.identicalPreviousResult = identicalPreviousResult;
	}
	private final LLVMIntersector intersector;
	private final Node<LLVMAbstractState> intersectionNode;

	private final LLVMIntersectionResult identicalPreviousResult;

	public LLVMIntermediateIntersectionResult getLegacyResult() {
		return legacyResult;
	}

	@Deprecated
	private final LLVMIntermediateIntersectionResult legacyResult;
	
	public Set<LLVMSEPath> getRespectedExecutionPaths() {
		return intersector.getExecutionPaths();
	}
	
	public Set<LLVMSEPath> getRespectedCycles() {
		return intersector.getRespectedCycles();
	}
	
	public Node<LLVMAbstractState> getReturnNode() {
		return intersector.getReturnNode();
	}
	
	public Node<LLVMAbstractState> getCallNode() {
		return intersector.getCallNode();
	}
	
	public Node<LLVMAbstractState> getIntersectedNode() {
		return intersectionNode;
	}

	public LLVMAbstractState getIntersectedState() {
		return getIntersectedNode().getObject();
	}

	public LLVMIntersectionResult getIdenticalPreviousResult() {
		return identicalPreviousResult;
	}

	public boolean intersectionYieldedResultIdenticalToPreviousIntersection() {
		return identicalPreviousResult != null;
	}
	
	LLVMSymbolicVariableRenamingRelationEvaluator getRenamingEvaluator() {
		return intersector.getRenamingEvaluator();
	}
	
	
	LLVMAllocationDeallocationEvaluator getAllocationDeallocationEvaluator() {
		return intersector.getDeallocationEvaluator();
	}
	
	LLVMUnchangedMemoryRelationEvaluator getUnchagedEvaluator() {
		return intersector.getUnchangedEvaluator();
	}
	
	
	//return allocation in intersected state _IDENTICAL_ to the call state, or null, if no such allocation found
	//one, in particular, it was not deallocated during the execution
	public LLVMAllocation getNotDeallocatedIntersectedStateAllocation(LLVMAllocation callStateAllocation) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getAllocations().contains(callStateAllocation);
		}
		
		LLVMAllocation iStateAlloc = intersector.getNotDeallocatedIntersectedStateAllocation(callStateAllocation);
		if(Globals.useAssertions && iStateAlloc != null) {
			assert intersectionNode.getObject().getAllocations().contains(iStateAlloc);
		}
		return iStateAlloc;
		
	}
	
	//return heap range in intersection identical to given one (i.e., guaranteed same values, but possibly other variable)
	public LLVMMemoryRange getUnchangedIntersectedStateMemoryRange(LLVMMemoryRange callStateMemoryRange) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getMemory().containsKey(callStateMemoryRange);
		}
		
		LLVMMemoryRange intersectedStateMemoryRange = intersector.getUnchangedIntersectedStateMemoryRange(callStateMemoryRange);
		
		if(Globals.useAssertions && intersectedStateMemoryRange != null) {
			assert intersectionNode.getObject().getMemory().containsKey(intersectedStateMemoryRange);
		}
		return intersectedStateMemoryRange;
	}
	
	
	//for callStateAllocation, getIntersectedStateAllocation msut return non-null value
	//returns true if it is guaranteed that the allocation was not modified (i.e., stored to)
	public boolean allocationUnchanged(LLVMAllocation callStateAllocation) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getAllocations().contains(callStateAllocation);
		}
		
		return intersector.allocationUnchanged(callStateAllocation);
	}
	
	public Set<LLVMSymbolicVariable> getIntersectionNamesForVariable(LLVMSymbolicVariable callStateVariable) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getSymbolicVariables().contains(callStateVariable);
		}
		Set<LLVMSymbolicVariable> intersectionVars =  intersector.getIntersectionNamesForVariable(callStateVariable);
	
		if(Globals.useAssertions) {
			assert getIntersectedNode().getObject().getSymbolicVariables().containsAll(intersectionVars);
		}
		
		return intersectionVars;
	}


	@Override
	public int hashCode() {
		int result = intersector != null ? intersector.hashCode() : 0;
		result = 31 * result + (intersectionNode != null ? intersectionNode.hashCode() : 0);
		result = 31 * result + (identicalPreviousResult != null ? identicalPreviousResult.hashCode() : 0);
		result = 31 * result + (legacyResult != null ? legacyResult.hashCode() : 0);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LLVMIntersectionResult other = (LLVMIntersectionResult) obj;
		return intersector == other.intersector
				&& intersectionNode == other.intersectionNode
				&& identicalPreviousResult == other.identicalPreviousResult;
	}
	

}
