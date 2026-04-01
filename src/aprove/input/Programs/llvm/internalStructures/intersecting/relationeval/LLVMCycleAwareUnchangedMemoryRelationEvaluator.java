package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.LinkedHashSet;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMAllocationDeallocationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMCycleAwareUnchangedMemoryRelationEvaluator extends LLVMUnchangedMemoryRelationEvaluator {

	private final LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator;
	private final LLVMAllocationDeallocationEvaluator allocationEvaluator;
	
	public LLVMCycleAwareUnchangedMemoryRelationEvaluator(
			LLVMImmutableFunctionGraph fg,
			Set<LLVMSEPath> executionPaths,
			LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator,
			LLVMAllocationDeallocationEvaluator allocationEvaluator,
			LLVMModule module,
			Abortion aborter) {
		super(fg, executionPaths, module, aborter);
		this.renamingEvaluator = renamingEvaluator;
		this.allocationEvaluator = allocationEvaluator;
	}



	
	
	LLVMSymbolicVariableRenamingRelationEvaluator getRenamingEvaluator() {
		return renamingEvaluator;
	}
	



	@Override
	protected UnchangedResult evaluateOnExecutionPathInternal(LLVMSEPath path, LLVMMemoryRange callStateRange) {
		int lastIndex = path.size() - 1;
		UnchangedResult result = new UnchangedResult();
		
		LLVMAbstractState callState = path.get(0).getObject();
		LLVMAssociationIndex assIndex = callState.getAssociatedAllocationIndex(callStateRange, aborter).x;
		
		if(assIndex == null || assIndex.x == null)
			throw new IllegalStateException("Could not find association for memory range");
		
		LLVMAllocation  callStateAllocation = callState.getAllocations().get(assIndex.x);
		AllocationResult allocationResultForPath = allocationEvaluator.evaluateOnPath(path, callStateAllocation);
		
		if(allocationResultForPath.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE
				&&  allocationResultForPath.getIndicesOnPathWhereAllocationWasPossiblyStoredTo().isEmpty()) {
			result.kind = UnchangedResultKind.UNCHANGED_LOST_DURING_MERGE;
			return result;
		}
		
		if(allocationResultForPath.kind != AllocationResultKind.NOT_FREED_LOST_DURING_MERGE
				&& allocationResultForPath.kind != AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION ) {
			result.kind = UnchangedResultKind.UNKNOWN;
			return result; 
		}
		
		
		LLVMMemoryRange currentRange = callStateRange;
		
		
		for (int curIndex = 0; curIndex < lastIndex; curIndex++) {
			Node<LLVMAbstractState> currentNode = path.get(curIndex);
			Node<LLVMAbstractState> nextNode = path.get(curIndex + 1);

			if(Helpers.hasMultipleOutgoingEdges(getFunctionGraph(), path, curIndex)) {
				Set<Pair<LLVMSEPath, Integer>> cyclePairs = Helpers.getCyclesLeadingOutOfPath(getFunctionGraph(), currentNode,path,curIndex);
				
				if (!cyclePairs.isEmpty()) {

					Pair<LLVMSymbolicVariable, LLVMSymbolicVariable> varPair = getVariablesFromRange(currentRange);
					LLVMMemoryInvariant currentInvariant = currentNode.getObject().getMemory().get(currentRange);
					Set<LLVMSymbolicVariable> symbolicVariablesUsedByInvariant = currentInvariant.getUsedReferences();

					boolean firstRangeVarConsistent = varPair.x == null
							|| getRenamingEvaluator().isVariableConsistetOnCycles(currentNode, varPair.x);
					boolean seconRangeVarConsistent = varPair.y != null
							|| getRenamingEvaluator().isVariableConsistetOnCycles(currentNode, varPair.y);
					boolean allInvariantVarsConsistent = symbolicVariablesUsedByInvariant.stream()
							.allMatch(v -> getRenamingEvaluator().isVariableConsistetOnCycles(currentNode, v));

					if (!(firstRangeVarConsistent && seconRangeVarConsistent && allInvariantVarsConsistent)) {
						result.kind = UnchangedResultKind.UNKNOWN;
						return result;
					}
				}
			}
			
			LLVMMemoryRange nextRange = handleSingleEdge(currentRange, getFunctionGraph(), currentNode, curIndex, nextNode, allocationResultForPath, result);
			if(result.kind != null) {
				if(Globals.useAssertions ) {
					assert result.kind != UnchangedResultKind.UNCHANGED_BECAME_TARGET_STATE_ENTRY;
				}
				return result;
			}	
			
			currentRange = nextRange;

		}
		Node<LLVMAbstractState> lastNode = path.get(lastIndex);
		LLVMAbstractState lastState = lastNode.getObject();
		
		if(!lastState.getMemory().containsKey(currentRange)) {
			throw new IllegalStateException("Something wrong");
		}
		
		result.targetStateMemoryRange = currentRange;
		result.kind = UnchangedResultKind.UNCHANGED_BECAME_TARGET_STATE_ENTRY;
		return result;
	}
	
	private LLVMMemoryRange handleSingleEdge(
			LLVMMemoryRange currentRenaming,
			LLVMFunctionGraph fg,
			Node<LLVMAbstractState> curNode,
			int curIndex,
			Node<LLVMAbstractState> nextNode,
			AllocationResult allocationResultForPath,
			UnchangedResult result //changed by this method
			) {
		
		if(Globals.useAssertions) {
			assert curNode.getObject().getMemory().keySet().contains(currentRenaming);
		}
		
		SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph = fg.getGraph();
		LLVMEdgeInformation edge = graph.getEdgeObject(curNode, nextNode);
		
		if(edge instanceof LLVMEvaluationInformation) {
			LLVMInstruction instr = curNode.getObject().getCurrentInstruction();
			
			 if (instr instanceof LLVMStoreInstruction) {
				if (storeMayShareWithMemoryRange(curNode, currentRenaming)) {
					result.kind = UnchangedResultKind.UNKNOWN;
					return null;
				} 

			}
			return handleRenaming(currentRenaming, fg, curNode, curIndex, nextNode, allocationResultForPath, result);
			
			
		} else if (edge instanceof LLVMRefinementInformation) {
			return handleRenaming(currentRenaming, fg, curNode, curIndex, nextNode, allocationResultForPath, result);
			
		} else if(edge instanceof LLVMInstantiationInformation) {
			return handleRenaming(currentRenaming, fg, curNode, curIndex, nextNode, allocationResultForPath, result);
		} else if(edge instanceof LLVMCallAbstractionEdge) { 
			return handleRenaming(currentRenaming, fg, curNode, curIndex, nextNode, allocationResultForPath, result);
		} else if(edge instanceof LLVMMethodSkipEdge) {
			LLVMIntersectionResult res =  ((LLVMMethodSkipEdge) edge).getIntersectionResult();
			LLVMMemoryRange intersectionRange = res.getUnchangedIntersectedStateMemoryRange(currentRenaming);
			
			
			if(intersectionRange == null) {
				if(allocationResultForPath.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE ||
						allocationResultForPath.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION) {	
					boolean notModifiedAfterThisPosition = allocationResultForPath.getIndicesOnPathWhereAllocationWasPossiblyStoredTo()
							.stream()
							.allMatch(modifiedAt -> modifiedAt < curIndex);
					
					if(notModifiedAfterThisPosition) {
						result.kind = UnchangedResultKind.UNCHANGED_LOST_TRACK_OF_NAME;
						return null;
					}
				}
				
				result.kind = UnchangedResultKind.UNKNOWN;
				return null;
			} else {
				return intersectionRange;
			}
			
			
		} else {
			throw new IllegalStateException("Unknown edge type");
		}
		
	}
	
	private LLVMMemoryRange handleRenaming(
			LLVMMemoryRange currentRenaming,
			LLVMFunctionGraph fg,
			Node<LLVMAbstractState> curNode,
			int curIndex,
			Node<LLVMAbstractState> nextNode,
			AllocationResult allocationResultForPath,
			UnchangedResult result) //changed by this method) 
			{
		Pair<LLVMMemoryRange,Boolean> nextRenaming = getRenamingOfMemoryRange(curNode,nextNode,currentRenaming);
		if(nextRenaming.x == null) {
			//lost track
			
			if((allocationResultForPath.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE ||
					allocationResultForPath.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION)
					) {
				boolean notModifiedAfterThisPosition = 
						allocationResultForPath.getIndicesOnPathWhereAllocationWasPossiblyStoredTo()
						.stream()
						.allMatch(modifiedAt -> modifiedAt < curIndex);
				
				if(notModifiedAfterThisPosition) {
					UnchangedResultKind kind = nextRenaming.y ? 
							UnchangedResultKind.UNCHANGED_LOST_DURING_MERGE : UnchangedResultKind.UNCHANGED_LOST_TRACK_OF_NAME;
					result.kind = kind;
					return null;
				} 
			}
			
			result.kind = UnchangedResultKind.UNKNOWN;
			return null;
		} else {
			return nextRenaming.x;
		}
	}
	
	

}
