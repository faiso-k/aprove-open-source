package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMAllocationDeallocationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMUnchangedMemoryRelationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Created by Frank on 02.06.2017.
 */
public abstract class LLVMAllocationDeallocationEvaluator {
	
	protected final Set<LLVMSEPath> executionPaths;
	protected final LLVMImmutableFunctionGraph fg;
	protected final LLVMModule module;
	
	protected final Map<Pair<LLVMSEPath, LLVMAllocation>,AllocationResult> cache; 
	
	public LLVMAllocationDeallocationEvaluator(LLVMImmutableFunctionGraph fg, Set<LLVMSEPath> executionPaths, LLVMModule module) {
		this.fg = fg;
		this.executionPaths = executionPaths;
		this.module = module;
		
		this.cache = new LinkedHashMap<>();
	}
	
	protected static enum AllocationResultKind {
		NOT_FREED_LOST_DURING_MERGE, //we know all potential stores
		NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION, //we know all potential stores
		UNKNOWN
		
	}
	
	protected static class AllocationResult {
		AllocationResultKind kind;
		
		
		//the index of the state whose OUTGOING instance/gen edge loses the allocation
		@Deprecated //not use
		Integer lostDuringGeneralizationAtIndex;
		
		//may also contain index where cycle starts which modifies the entry
		//only non-null if 
				//   result == NOT_FREED_LOST_DURING_MERGE
				//or result ==  NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION
		private Set<Integer> possibilyModifedAtIndex;
		
		void addIndexWherePossiblyStoredToAllocation(int modificationIndex) {
			if(possibilyModifedAtIndex == null) {
				possibilyModifedAtIndex = new LinkedHashSet<>();
			}
			possibilyModifedAtIndex.add(modificationIndex);
		}
		
		Set<Integer> getIndicesOnPathWhereAllocationWasPossiblyStoredTo() {
			if(kind == null 
					|| (kind != AllocationResultKind.NOT_FREED_LOST_DURING_MERGE
					&& kind != AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION)) {
				throw new IllegalStateException("Do not ask for this for an unknown allocation result");
			}
			if(possibilyModifedAtIndex == null)
				return Collections.emptySet();
			else
				return possibilyModifedAtIndex;
						
		}
		
		
		LLVMAllocation becameAllocationInLastStateOfPath;
		
		
		//only non-null if 
		//   result == NOT_FREED_LOST_DURING_MERGE
		//or result ==  NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION
		@Deprecated //not use
		List<LLVMAllocation> renamings;
	}
	
	protected Set<LLVMSEPath> getExecutionPaths() {
		return executionPaths;
	}
	
	protected LLVMImmutableFunctionGraph getFunctionGraph() {
		return fg;
	}

	// returns <x,y>: x = not deallocated? y= lost on all paths ? (only relevant when x = true)
	@Deprecated
    public abstract Pair<Boolean,Boolean> notDeallocated(LLVMAllocation callStateAllocation);
	
	public boolean allocationLostDuringMergeWithoutDeallocationOnAllPaths(LLVMAllocation allocationAtNodeIndex) {
		for(LLVMSEPath executionPath : getExecutionPaths()) {
			AllocationResult allocRes = evaluateOnPath(executionPath,allocationAtNodeIndex);
			if(allocRes.kind != AllocationResultKind.NOT_FREED_LOST_DURING_MERGE)
				return false;
		}
		return true;
	}
	
	//null means "false"
	public LLVMAllocation allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(LLVMAllocation callStateAllocation) {
		LLVMAllocation returnStateAlloc = null;
		for(LLVMSEPath executionPath : getExecutionPaths()) {
			AllocationResult allocRes = evaluateOnPath(executionPath,callStateAllocation);
			if(allocRes.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION) {
				if(returnStateAlloc != null) {
					if(!returnStateAlloc.equals(allocRes.becameAllocationInLastStateOfPath)) {
						return null;
					}
				} else {
					returnStateAlloc = allocRes.becameAllocationInLastStateOfPath;
				}
				
			} else {
				return null;
			}
		}
		return returnStateAlloc;
	}
	
	public boolean allocationNotDeallocatedAndNotStoredToOnAllPaths(LLVMAllocation callStateAllocation) {
		for(LLVMSEPath executionPath : getExecutionPaths()) {
			AllocationResult allocRes = evaluateOnPath(executionPath,callStateAllocation);
			if(!(allocRes.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE
					|| allocRes.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION
					&& (allocRes.getIndicesOnPathWhereAllocationWasPossiblyStoredTo().isEmpty()))) {
				return false;
			}
		}
		return true;
	}
	
	
	
	
	protected AllocationResult evaluateOnPath(LLVMSEPath path, LLVMAllocation firstStateAllocation) {
		AllocationResult result = null;
		if(LLVMDebuggingFlags.CACHE_INTERSECTION_PATH_EVALUATOR_RESULTS) {
			result = cache.get(new Pair<>(path,firstStateAllocation));
		}
		if(result == null) {
			result =  evaluateOnExecutionPathInternal(path,  firstStateAllocation);
			if(LLVMDebuggingFlags.CACHE_INTERSECTION_PATH_EVALUATOR_RESULTS) {
				cache.put(new Pair<>(path,firstStateAllocation),result);
			}
		}
		return result;
		
	}
    
    protected abstract AllocationResult evaluateOnExecutionPathInternal(LLVMSEPath executionPath, LLVMAllocation callStateAllocation);
    
    
    //does not respect consistency of variable names along cycles, i.e., only local renaming
    //to be called to find out how an allocation changed IF IT WAS NOT DEALLOCATED AT curNode!
    //Ok to use on evaluation, refinement, instantiation (and gen.), and call abstraction edges edges
    //returns tuple (x,y), where x is null or the renaming of curStateAllocation in nextNode
    //if x is null y indicates whether it was lost during a generalization (TRUE) or we simply don't know how the allocation was renamed (FALSE)
    protected Pair<LLVMAllocation,Boolean> getRenamingOfAllocationOnSingleEdge(LLVMImmutableFunctionGraph fg, Node<LLVMAbstractState> curNode, Node<LLVMAbstractState> nextNode, LLVMAllocation curStateAllocation) {
    	SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> graph = fg.getGraph();
    	LLVMEdgeInformation edge = graph.getEdgeObject(curNode, nextNode);
    	
    	LLVMAbstractState nextState = nextNode.getObject();
    	List<LLVMAllocation> nextAllocations = nextState.getAllocations();
    	
    	if(edge instanceof LLVMEvaluationInformation ||
    			edge instanceof LLVMRefinementInformation) {
    		if(nextAllocations.contains(curStateAllocation)) {
    			return new Pair<>(curStateAllocation,null);
    		} else {
    			Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> allocVars = getVariablesFromAllocation(curStateAllocation);
    			
    			Set<? extends LLVMSimpleTerm> lowerBoundRenaming = allocVars.x == null ? Collections.singleton(curStateAllocation.x) :
    				LLVMSymbolicVariableRenamingRelationEvaluator.getRenamingsOfSingleVariableOnSingleEdge(curNode, nextNode, fg, module, allocVars.x);
    			
    			Set<? extends LLVMSimpleTerm> upperBoundRenaming = allocVars.y == null ? Collections.singleton(curStateAllocation.y) :
    				LLVMSymbolicVariableRenamingRelationEvaluator.getRenamingsOfSingleVariableOnSingleEdge(curNode, nextNode, fg, module, allocVars.y);
    			
    			for(LLVMSimpleTerm lower : lowerBoundRenaming) {
    				for(LLVMSimpleTerm upper : upperBoundRenaming) {
    					LLVMAllocation curRenaming = new LLVMAllocation(lower, upper);
    					
    					if(nextAllocations.contains(curRenaming)) {
    						return new Pair<>(curRenaming,null);
    					}
    					
    				}
    			}
    			return new Pair<>(null,false);
    			
    		}
    	} else if(edge instanceof LLVMInstantiationInformation) {
    		LLVMInstantiationInformation instantiationEdge = (LLVMInstantiationInformation) edge;
			Map<LLVMSimpleTerm, LLVMSimpleTerm> referenceCorrespondenceMap = instantiationEdge
					.getReferenceCorrespondenceMap();
			
			Map<LLVMSymbolicVariable,LLVMSimpleTerm> convertedReferenceCorrespondenceMap =
					convert(referenceCorrespondenceMap);
			Substitution subst = Substitution.toSubstitution(convertedReferenceCorrespondenceMap);
			
			
			for(LLVMAllocation nextStateAllocation : nextAllocations) {
				LLVMAllocation renamedToCurState = nextStateAllocation.applySubstitution(subst);
				if(renamedToCurState.equals(curStateAllocation)) {
					return new Pair<>(nextStateAllocation,null);
				}
			}
			
			//not found
			return new Pair<>(null,true);
			
    	} else if(edge instanceof LLVMCallAbstractionEdge) {
    		if(nextAllocations.contains(curStateAllocation)) {
    			return new Pair<>(curStateAllocation,null);
    		} else {
    			return new Pair<>(null,true);
    		}
    	} else {
    		throw new IllegalArgumentException();
    	}
    	
    	
    }
    
    //must be at a free instruction
    //node must be evaluated, i.e., should have outgoing eval edge
    //alloc must be an malloc  allocation of it
    //we know the definite answer because we enforece memory safety for evaluation of free for summarized functions
    protected boolean freesGivenAllocation(Node<LLVMAbstractState> node, LLVMAllocation mallocAlloc) {
    	if(!node.getObject().getAllocatedByMalloc().contains(mallocAlloc)) {
    		throw new IllegalArgumentException();
    	}
    	
    	
    	LLVMAllocation freedAllocation = getFunctionGraph().getMemoryChangeTracker().getAllocationFreedByFreeEvaluation(node);
    	
    	return freedAllocation.equals(mallocAlloc);
    	
    }
    
    //must be at a store instruction
    //node must be evaluated, i.e., should have outgoing eval edge
    //alloc must be an  allocation of it
    //we know the definite answer because we enforce memory safety for evaluation of free for summarized functions
    protected boolean storesToGivenAllocation(Node<LLVMAbstractState> node, LLVMAllocation alloc) {
    	if(!node.getObject().getAllocations().contains(alloc)) {
    		throw new IllegalArgumentException();
    	}
    	
    	LLVMAllocation modifiedAlloc = getFunctionGraph().getMemoryChangeTracker().getAllocationModifiedByStoreEvaluation(node);
    	return modifiedAlloc.equals(alloc);
    }
    
	public static Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> getVariablesFromAllocation(LLVMAllocation allocation) {
		LLVMSymbolicVariable lower = null;
		LLVMSymbolicVariable upper = null;
		
		if(allocation.x instanceof LLVMSymbolicVariable) {
			lower = (LLVMSymbolicVariable) allocation.x; 
		}
		
		if(allocation.y instanceof LLVMSymbolicVariable) {
			upper = (LLVMSymbolicVariable) allocation.y; 
		}
		return new Pair<>(lower,upper);
	}
	
	
	private Map<LLVMSymbolicVariable,LLVMSimpleTerm> convert(Map<LLVMSimpleTerm,LLVMSimpleTerm> referenceCorrespondenceMap) {
		Map<LLVMSymbolicVariable,LLVMSimpleTerm> result = new LinkedHashMap<>();
		for(Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : referenceCorrespondenceMap.entrySet()) {
			if(entry.getKey() instanceof LLVMSymbolicVariable) {
				LLVMSymbolicVariable keyVar = (LLVMSymbolicVariable) entry.getKey();
				result.put(keyVar, entry.getValue());
			}
		}
		return result;
	}
    
	
	//note that we do not check here if the allocation was modified before being lost
	protected  boolean allocationLostDuringGeneralizationOnExecutionPathPrefix(
			LLVMSEPath executionPathPrefix,
			LLVMAllocation callStateAllocation) {
		LLVMAllocation curAllocRenaming = callStateAllocation;
		Node<LLVMAbstractState> curNode = executionPathPrefix.get(0);
		for(int stateIndex = 0;stateIndex < executionPathPrefix.size() - 1;stateIndex++) {
			Node<LLVMAbstractState> nextNode = executionPathPrefix.get(stateIndex+1);
			LLVMAbstractState nextState = nextNode.getObject();
			//List<LLVMAllocation> nextStateAllocs = nextState.getAllocations();
			
			//LLVMEdgeInformation edgeToNext = fg.getGraph().getEdgeObject(curNode,nextNode);
			
			
			Pair<LLVMAllocation,Boolean> nextRenaming = getRenamingOfAllocationOnSingleEdge(fg,curNode,nextNode,curAllocRenaming);
			if(nextRenaming.x == null) {
				if(nextRenaming.y) {
					return true;
				} else {
					return false;
				}
			} else {
				curAllocRenaming = nextRenaming.x;
			} 

			
			curNode = nextNode;
			
		}
		
		return false;
	}
	
}
