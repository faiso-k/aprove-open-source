package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMAllocationDeallocationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public abstract class LLVMUnchangedMemoryRelationEvaluator {

    //idea: it's okay to see if the desired memory range still points to the same value (modulo remaining) in the last state of the execution path
    //If not, it may want to follow a more traditional approach:
    //track the PT-entry along the path, modulo renaming
    //if it gets generalized away, we could still try to see if the containing allocation is never written to
    //if we don't know the allocation, we could just see if there are no store and free instructions reachable

	protected final LLVMImmutableFunctionGraph fg;
	protected final Set<LLVMSEPath> executionPaths;
	protected final Abortion aborter;
	protected final LLVMModule module;
	
	protected final Map<Pair<LLVMSEPath, LLVMMemoryRange>,UnchangedResult> cache; 
	
	public LLVMUnchangedMemoryRelationEvaluator(LLVMImmutableFunctionGraph fg, Set<LLVMSEPath> executionPaths, LLVMModule module, Abortion aborter) {
		this.fg = fg;
		this.executionPaths = executionPaths;
		this.aborter = aborter;
		this.module = module;
		
		this.cache = new LinkedHashMap<>();
	}
	
	protected static enum UnchangedResultKind {
		UNCHANGED_LOST_DURING_MERGE,
		UNCHANGED_BECAME_TARGET_STATE_ENTRY,
		UNCHANGED_LOST_TRACK_OF_NAME, //we can guarantee that the range was not changed, but we don't know the range in the return state it corresponds to (there may not even be one)
		UNKNOWN
	}
	
	protected static class UnchangedResult {
		UnchangedResultKind kind;
		
		LLVMMemoryRange targetStateMemoryRange; //only valid if kind is UNCHANGED_BECAME_TARGET_STATE_ENTRY
	}
	
	protected LLVMFunctionGraph getFunctionGraph() {
		return fg;
	}

    
    public boolean unchanged(LLVMMemoryRange callStateRange) {
        if (callStateRange instanceof LLVMMemoryRecursiveRange) {
            LLVMMemoryRecursiveRange callRecRange = (LLVMMemoryRecursiveRange) callStateRange;
            // Only return true if not accessible from vars in function frame of call state. Otherwise return false.
            LLVMAbstractState callState = getExecutionPaths().iterator().next().get(0).getObject();
            for (String var : callState.getProgramVariables().keySet()) {
                LLVMSymbolicVariable ref = callState.getSymbolicVariableForProgramVariable(var);
                if (callRecRange.getFromRef().equals(ref) || callRecRange.getToRef().equals(ref) || callRecRange.getLength().equals(ref)) {
                    return false;
                }
                for (LLVMMemoryRange range : callState.getMemory().keySet()) {
                    if (range.getFromRef().equals(ref) || range.getToRef().equals(ref)) {
                        return false;
                    }
                }
            }
            return true;
        }
    	for(LLVMSEPath path : getExecutionPaths()) {
    		UnchangedResult res = evaluateOnPath(path,callStateRange);
    		
    		if(res.kind != UnchangedResultKind.UNCHANGED_LOST_DURING_MERGE
    				&& res.kind != UnchangedResultKind.UNCHANGED_BECAME_TARGET_STATE_ENTRY
    				&& res.kind != UnchangedResultKind.UNCHANGED_LOST_TRACK_OF_NAME)
    			return false;
    	}
    	
    	return true;
    }
    
    public LLVMMemoryRange turnedIntoReturnStateRangeOnAllPaths(LLVMMemoryRange callStateRange) {
    	LLVMMemoryRange returnStateRange = null;
		for(LLVMSEPath executionPath : getExecutionPaths()) {
			UnchangedResult unchangedRes = evaluateOnPath(executionPath,callStateRange);
			if(unchangedRes.kind == UnchangedResultKind.UNCHANGED_BECAME_TARGET_STATE_ENTRY) {
				if(returnStateRange != null) {
					if(!returnStateRange.equals(unchangedRes.targetStateMemoryRange)) {
						return null;
					}
				} else {
					returnStateRange = unchangedRes.targetStateMemoryRange;;
				}
				
			} else {
				return null;
			}
		}
		return returnStateRange;
    }
    
    public UnchangedResult evaluateOnPath(LLVMSEPath path, LLVMMemoryRange callStateRange) {
    	UnchangedResult result = null;
		if(LLVMDebuggingFlags.CACHE_INTERSECTION_PATH_EVALUATOR_RESULTS) {
			result = cache.get(new Pair<>(path,callStateRange));
		}
		if(result == null) {
			result =  evaluateOnExecutionPathInternal(path,  callStateRange);
			if(LLVMDebuggingFlags.CACHE_INTERSECTION_PATH_EVALUATOR_RESULTS) {
				cache.put(new Pair<>(path,callStateRange),result);
			}
		}
		return result;
    }
    
    protected Set<LLVMSEPath> getExecutionPaths() {
    	return executionPaths;
    }
    
    protected abstract UnchangedResult evaluateOnExecutionPathInternal(LLVMSEPath path, LLVMMemoryRange callStateRange);

    
    //does not respect consistency of variable names along cycles, i.e., only local renaming
    //to be called to find out how an allocation changed IF IT WAS NOT MODIFIED BY STORE AT curNode!
    //Ok to use on evaluation, refinement, instantiation (and gen.), call abstraction edges
    //does not support method skip edges!
    //returns tuple (x,y), where x is null or the renaming of curStateMemoryRange in nextNode
    //if x is null y indicates whether it was lost during a generalization (TRUE) or we simply don't know how the memory ragne was renamed (FALSE)
    protected Pair<LLVMMemoryRange,Boolean> getRenamingOfMemoryRange(Node<LLVMAbstractState> curNode, Node<LLVMAbstractState> nextNode, LLVMMemoryRange curStateMemoryRange) {
    	SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> graph = fg.getGraph();
    	LLVMEdgeInformation edge = graph.getEdgeObject(curNode, nextNode);
    	
    	LLVMAbstractState nextState = nextNode.getObject();
    	Map<LLVMMemoryRange,LLVMMemoryInvariant> nextHeap = nextState.getMemory();
    	
    	if(edge instanceof LLVMEvaluationInformation ||
    			edge instanceof LLVMRefinementInformation) {
    		if(nextHeap.containsKey(curStateMemoryRange)) {
    			return new Pair<>(curStateMemoryRange,null);
    		} else {
    			Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> rangeVars = getVariablesFromRange(curStateMemoryRange);
    			
    			Set<? extends LLVMSimpleTerm> lowerBoundRenaming = rangeVars.x == null ? Collections.singleton(curStateMemoryRange.getFromRef()) :
    				LLVMSymbolicVariableRenamingRelationEvaluator.getRenamingsOfSingleVariableOnSingleEdge(curNode, nextNode, fg, module, rangeVars.x);
    			
    			Set<? extends LLVMSimpleTerm> upperBoundRenaming = rangeVars.y == null ? Collections.singleton(curStateMemoryRange.getToRef()) :
    				LLVMSymbolicVariableRenamingRelationEvaluator.getRenamingsOfSingleVariableOnSingleEdge(curNode, nextNode, fg, module, rangeVars.y);
    			
    			for(LLVMSimpleTerm lower : lowerBoundRenaming) {
    				for(LLVMSimpleTerm upper : upperBoundRenaming) {
    					LLVMMemoryRange curRenaming = new LLVMMemoryRange(lower, upper, curStateMemoryRange.getType(), curStateMemoryRange.getUnsigned());
    					
    					if(nextHeap.containsKey(curRenaming)) {
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

			
			for(LLVMMemoryRange nextStateRange: nextHeap.keySet()) {
				Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> rangeVars = getVariablesFromRange(nextStateRange);
				
				
				LLVMSimpleTerm lower = null;
				LLVMSimpleTerm upper = null;
				if(rangeVars.x != null) {
					lower = referenceCorrespondenceMap.get(rangeVars.x);
				} else {
					lower = nextStateRange.getFromRef();
				}
				if(rangeVars.y != null) {
					upper = referenceCorrespondenceMap.get(rangeVars.y);
				} else {
					upper = nextStateRange.getToRef();
				}
				
				
				LLVMMemoryRange renamedToCurState = new LLVMMemoryRange(lower, upper, curStateMemoryRange.getType(), curStateMemoryRange.getUnsigned());
				if(renamedToCurState.equals(curStateMemoryRange)) {
					return new Pair<>(nextStateRange,null);
				}
			}
			
			//not found
			return new Pair<>(null,true);
			
    	} else if(edge instanceof LLVMCallAbstractionEdge) {
    		if(nextHeap.containsKey(curStateMemoryRange)) {
    			return new Pair<>(curStateMemoryRange,null);
    		} else {
    			return new Pair<>(null,true);
    		}
    	} else {
    		throw new IllegalArgumentException();
    	}
    	
    }
    
    
    //must be at a store instruction
    //node must be evaluated, i.e., should have outgoing eval edge
    //memRange must be an memory range with a heap entry in node
    //we know the definite answer because we enforece memory safety for evaluation of store for summarized functions
    protected boolean storeMayShareWithMemoryRange(Node<LLVMAbstractState> node, LLVMMemoryRange memRange) {
    	if(!node.getObject().getMemory().keySet().contains(memRange)) {
    		throw new IllegalArgumentException();
    	}
    	
    	Set<LLVMMemoryRange> possiblyInvalidatedRanges = getFunctionGraph().getMemoryChangeTracker().getMemoryRangesInvalidatedByStore(node);
    	
    	return possiblyInvalidatedRanges.contains(memRange);
    }
    
	public static Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> getVariablesFromRange(LLVMMemoryRange range) {
		LLVMSymbolicVariable lower = null;
		LLVMSymbolicVariable upper = null;
		
		if(range.getFromRef() instanceof LLVMSymbolicVariable) {
			lower = (LLVMSymbolicVariable) range.getFromRef(); 
		}
		
		if(range.getToRef()instanceof LLVMSymbolicVariable) {
			upper = (LLVMSymbolicVariable) range.getToRef(); 
		}
		return new Pair<>(lower,upper);
	}
}
