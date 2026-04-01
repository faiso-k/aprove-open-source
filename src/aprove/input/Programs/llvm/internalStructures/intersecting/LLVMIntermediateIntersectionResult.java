package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author Frank Emrich, cryingshadow
 * @version $Id$
 */
public class LLVMIntermediateIntersectionResult {

	Node<LLVMAbstractState> callNode;
	Node<LLVMAbstractState> returnNode;
	
	//Node<LLVMAbstractState> intersectionNode;
	
    

	Set<LLVMRelation> expressions;



	Set<LLVMSymbolicVariable> freshReferences;

    //LLVMAbstractState intersectedState;

    LLVMAbstractState returnState;

    LLVMAbstractState callState;

    Set<LLVMSEPath> respectedPathsFromCallToReturnState;
    
    


	/**
	 * Malloc Allocations of the call state that were not freed on the path from call to return state
	 * 
	 * Corresponds to the Set "ND" in the LLVM Recursion Paper
	 */
	Set<LLVMAllocation> preserverdMallocAllocationsOfCallState;
	
	
	/**
	 * Subset of <code>preserverdMallocAllocationsOfCallState</code> of allocations that were lost on all respected paths during generalizations
	 */
	Set<LLVMAllocation> preserverdMallocAllocationsOfCallStateLostOnPaths;
	


	/**
	 * The MemoryRanges (=address ranges) of heap entries of the call state that we can guarantee not to be changed
	 * 
	 * Corresponds to the Set "U" in the LLVM Recursion Paper
	 */
	Set<LLVMMemoryRange> preserverdCallStateHeapEntrieRanges;

	/**
	 * Maps the indices of malloc allocations of the return state to their "new" index in the intersected state
	 */
	@Deprecated
	Map<Integer, Integer> mallocAllocationIndicesReturnToIntersection;

	

	/**
	 * Corresponds to "R" in the LLVM Recursion Paper
	 */
	Map<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> renamingsOnPathsFromCallToReturnState;

	public Map<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> getRenamingsOnPathsFromCallToReturnState() {
		return renamingsOnPathsFromCallToReturnState;
	}

	/**
	 * Uses the known renamings from return to call state, if possible. Otherwise, use fresh variable.
	 */
	Map<LLVMSymbolicVariable, LLVMSymbolicVariable> variableMappingFromReturnToIntersectedState;


	
	/** Maps stack allocations (topmost or lower stack frames) to allocations in the call state, or null, if no correspondence is known
	 * 
	 */
	@Deprecated
	Map<LLVMAllocation, LLVMAllocation> renamingMapOfStackAllocationsReturnStateToCallState;
	
	public Set<LLVMAllocation> getPreserverdMallocAllocationsOfCallState() {
		return preserverdMallocAllocationsOfCallState;
	}

	public Set<LLVMMemoryRange> getPreserverdCallStateHeapEntrieRanges() {
		return preserverdCallStateHeapEntrieRanges;
	}
	
	/*public Node<LLVMAbstractState> getIntersectionNode() {
		return intersectionNode;
	}*/


	public Node<LLVMAbstractState> getCallNode() {
		return callNode;
	}

	public Node<LLVMAbstractState> getReturnNode() {
		return returnNode;
	}
	
	public Set<LLVMSEPath> getRespectedPathsFromCallToReturnState() {
		return respectedPathsFromCallToReturnState;
	}
	
    public Set<LLVMRelation> getExpressions() {
		return expressions;
	}

	/*@Override
	public String toString() {
		return "LLVMIntersectionResult [" + (callNode != null ? "callNode=" + callNode.getNodeNumber() + ", " : "")
				+ (returnNode != null ? "returnNode=" + returnNode.getNodeNumber() + ", " : "")
				+ (intersectionNode != null ? "intersectionNode=" + intersectionNode.getNodeNumber() + ", " : "")
				+ (respectedPathsFromCallToReturnState != null
						? "respectedPathsFromCallToReturnState=" + respectedPathsFromCallToReturnState : "")
				+ "]";
	}*/
    
    
}
