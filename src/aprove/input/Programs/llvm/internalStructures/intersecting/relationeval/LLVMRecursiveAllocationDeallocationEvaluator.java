package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import aprove.Globals;
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
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMRecursiveAllocationDeallocationEvaluator extends LLVMAllocationDeallocationEvaluator {

public LLVMRecursiveAllocationDeallocationEvaluator(LLVMImmutableFunctionGraph fg, Set<LLVMSEPath> executionPaths, LLVMModule module) {
		super(fg, executionPaths, module);
		// TODO Auto-generated constructor stub
	}


private static class StackEntry {
		
		
		public StackEntry(LLVMSEPath path, int nodeIndexOnPath, LLVMAllocation alloc) {
			super();
			this.path = path;
			this.nodeIndexOnPath = nodeIndexOnPath;
			this.alloc = alloc;
		}
		
		//TODO FEM: use == based equals on other occasions for LLMSEPath, too?
		
		
		
		LLVMSEPath path;
		int nodeIndexOnPath;
		LLVMAllocation alloc;
		@Override
		
		//respects path based on identity
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + nodeIndexOnPath;
			result = prime * result + ((path == null) ? 0 : System.identityHashCode(path));
			result = prime * result + ((alloc == null) ? 0 : alloc.hashCode());
			return result;
		}
		
		//compares path based on identity
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			StackEntry other = (StackEntry) obj;
			if (nodeIndexOnPath != other.nodeIndexOnPath)
				return false;
			if(path != other.path)
			if (alloc == null) {
				if (other.alloc != null)
					return false;
			} else if (!alloc.equals(other.alloc))
				return false;
			return true;
		}
	}
	

	
	@Override
	public Pair<Boolean, Boolean> notDeallocated(LLVMAllocation callStateAllocation) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	protected AllocationResult evaluateOnExecutionPathInternal(LLVMSEPath executionPath, LLVMAllocation callStateAllocation) {
		Node<LLVMAbstractState> callNode = executionPath.get(0);
		LLVMAbstractState callState = callNode.getObject();
		return evaluateOnPath(executionPath,0,callStateAllocation,callState.getAllocatedByMalloc().contains(callStateAllocation),new LinkedHashSet<>());
	}
	
	//keep loop structure in sync with recursive renaming evaluator (uses similar loop)
	//allocationAtNodeIndex may be null
	private AllocationResult evaluateOnPath(LLVMSEPath path, int nodeIndexOnPath, LLVMAllocation allocationAtNodeIndex, boolean isMallocAllocation, LinkedHashSet<StackEntry> stack) {
		StackEntry entryForThisInvocation = new StackEntry(path, nodeIndexOnPath, allocationAtNodeIndex);
		boolean isCyclic = path.isCyclic();
		
		
		AllocationResult result = new AllocationResult();
		Node<LLVMAbstractState> curNode = path.get(nodeIndexOnPath);
		if(stack.contains(entryForThisInvocation)) {
			//We do not want to descend into the same cycle again
			if(isCyclic) {
				//"everything ok" signal.
				result.becameAllocationInLastStateOfPath = allocationAtNodeIndex;
				//result.possibilyModifedAtIndex = Collections.emptySet();
				result.kind = AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION;
				return result;
			} else {
				throw new IllegalStateException("saw non-cyclic path twice. what to do?");
			}
			
		}
		stack.add(entryForThisInvocation);

		
		LLVMAllocation currentRenaming = allocationAtNodeIndex;
		
		
		
		int lastIndexOfPath = path.size() - 1;
		
		if(Globals.useAssertions && isCyclic) {
			assert nodeIndexOnPath != lastIndexOfPath;
		}
		int curIndex = nodeIndexOnPath;
		int stopIndex = lastIndexOfPath;
		if(isCyclic) {
			if(nodeIndexOnPath == 0) {
				stopIndex = lastIndexOfPath;
			} else {
				stopIndex = nodeIndexOnPath;
			}
			
		}
		boolean first = true;
		
		while(curIndex != stopIndex || first) {
			first = false;
			
			int nextIndex = -1;
			if(isCyclic && curIndex == lastIndexOfPath) {
				nextIndex = 1; //0 is the same node as the one at the current index
			} else {
				nextIndex = curIndex + 1;
			}
			Node<LLVMAbstractState> nextNode = path.get(nextIndex);
			
			
			
			
			//logic here

			if(Helpers.hasMultipleOutgoingEdges(getFunctionGraph(), path, curIndex)) {
				Set<Pair<LLVMSEPath, Integer>> cyclePairs = Helpers.getCyclesLeadingOutOfPath(getFunctionGraph(), curNode,path,curIndex);
				for (Pair<LLVMSEPath, Integer> p : cyclePairs) {
					AllocationResult resForCycle = evaluateOnPath(p.x,p.y,currentRenaming,isMallocAllocation,new LinkedHashSet<>(stack));
					if(resForCycle.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION
							&& resForCycle.becameAllocationInLastStateOfPath.equals(currentRenaming)) {
						if(!resForCycle.getIndicesOnPathWhereAllocationWasPossiblyStoredTo().isEmpty()) {
							result.addIndexWherePossiblyStoredToAllocation(curIndex);
						}
					} else {
						result.kind = AllocationResultKind.UNKNOWN;
						//result.possibilyModifedAtIndex = null;
						result.renamings = null;
						return result;
					}
					
				}
			}
			
			LLVMAllocation nextAlloc = handleSingleEdge(currentRenaming, getFunctionGraph(), curNode, curIndex, nextNode, isMallocAllocation, result);
			if(result.kind != null) {
				return result;
			}

			
			currentRenaming = nextAlloc;
			//end logic
			
			curNode = nextNode;
			curIndex = nextIndex;
			
			
		}
		
		result.kind = AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION;
		result.becameAllocationInLastStateOfPath = currentRenaming;
		if(Globals.useAssertions) {
			assert curNode.getObject().getAllocations().contains(currentRenaming);
		}
		return result;
	}
	
	
	private LLVMAllocation handleSingleEdge(
			LLVMAllocation currentRenaming,
			LLVMImmutableFunctionGraph fg,
			Node<LLVMAbstractState> curNode,
			int curIndex,
			Node<LLVMAbstractState> nextNode,
			boolean isMallocAllocation,
			AllocationResult result //changed by this method
			) {
		
		if(Globals.useAssertions) {
			assert curNode.getObject().getAllocations().contains(currentRenaming);
		}
		
		SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph = fg.getGraph();
		LLVMEdgeInformation edge = graph.getEdgeObject(curNode, nextNode);
		
		if(edge instanceof LLVMEvaluationInformation) {
			LLVMInstruction instr = curNode.getObject().getCurrentInstruction();
			
			if (instr instanceof LLVMCallInstruction && isMallocAllocation
					&& ((LLVMCallInstruction) instr).isFreeCall()) {
				if (freesGivenAllocation(curNode, currentRenaming)) {
					result.kind = AllocationResultKind.UNKNOWN;
					//result.possibilyModifedAtIndex = null;
					//result.renamings = null;
					return null;
				}

			} else if (instr instanceof LLVMStoreInstruction) {
				if (storesToGivenAllocation(curNode, currentRenaming)) {
					result.addIndexWherePossiblyStoredToAllocation(curIndex);
				}

			}
			Pair<LLVMAllocation,Boolean> nextRenaming = getRenamingOfAllocationOnSingleEdge(fg,curNode,nextNode, currentRenaming);
			if(nextRenaming.x == null) {
				//lost track
				result.kind = AllocationResultKind.UNKNOWN;
				//result.possibilyModifedAtIndex = null;
				//result.renamings = null;
				return null;
			} else {
				//result.renamings.add(nextRenaming.x);
				return nextRenaming.x;
			}
			
			
		} else if (edge instanceof LLVMRefinementInformation) {
			Pair<LLVMAllocation,Boolean> nextRenaming = getRenamingOfAllocationOnSingleEdge(fg,curNode,nextNode, currentRenaming);
			if(nextRenaming.x == null) {
				//lost track
				result.kind = AllocationResultKind.UNKNOWN;
				//result.possibilyModifedAtIndex = null;
				result.renamings = null;
				return null;
			} else {
				//result.renamings.add(nextRenaming.x);
				return nextRenaming.x;
			}
			
		} else if(edge instanceof LLVMInstantiationInformation) {
			Pair<LLVMAllocation,Boolean> nextRenaming = getRenamingOfAllocationOnSingleEdge(fg,curNode,nextNode, currentRenaming);
			if(nextRenaming.x == null) {
				if(nextRenaming.y) {
					//generalized away
					result.kind = AllocationResultKind.NOT_FREED_LOST_DURING_MERGE;
					//result.lostDuringGeneralizationAtIndex = curIndex;
					return null;
				} else {
					//lost
					result.kind = AllocationResultKind.UNKNOWN;
					//result.possibilyModifedAtIndex = null;
					//result.renamings = null;
					return null;
				}
			} else {
				//result.renamings.add(nextRenaming.x);
				return nextRenaming.x;
			}
		} else if(edge instanceof LLVMMethodSkipEdge) {
			LLVMIntersectionResult res =  ((LLVMMethodSkipEdge) edge).getIntersectionResult();
			LLVMAllocation nextAlloc = res.getNotDeallocatedIntersectedStateAllocation(currentRenaming);
			
			if(nextAlloc == null) {
				result.kind = AllocationResultKind.UNKNOWN;
				//result.possibilyModifedAtIndex = null;
				//result.renamings = null;
				return null;
			} else {
				if(!res.allocationUnchanged(currentRenaming)) {
					result.addIndexWherePossiblyStoredToAllocation(curIndex);
				}
				//result.renamings.add(nextAlloc);
				return nextAlloc;
			}
			
			
		} if(edge instanceof LLVMCallAbstractionEdge) {
			Pair<LLVMAllocation,Boolean> nextRenaming = getRenamingOfAllocationOnSingleEdge(fg,curNode,nextNode, currentRenaming);
			if(nextRenaming.x == null) {
				if(nextRenaming.y) {
					//generalized away
					result.kind = AllocationResultKind.NOT_FREED_LOST_DURING_MERGE;
					//result.lostDuringGeneralizationAtIndex = curIndex;
					return null;
				} else {
					//lost
					result.kind = AllocationResultKind.UNKNOWN;
					//result.possibilyModifedAtIndex = null;
					//result.renamings = null;
					return null;
				}
			} else {
				//result.renamings.add(nextRenaming.x);
				return nextRenaming.x;
			}
		} else {
			throw new IllegalStateException("Unknown edge type");
		}
		
	}
	
	
	
	
	


	
}
