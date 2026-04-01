package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Intersect a call state and a return state for recursion.
 * @author Frank Emrich, cryingshadow
 */

public class LLVMIntersector implements Immutable {

	//@Deprecated
	//protected LLVMIntermediateIntersectionResult intermediateResult;
	//@Deprecated
	//protected LLVMSEGraph seGraph;
	protected LLVMModule module;
	
	protected Node<LLVMAbstractState> entryNode;
	protected Node<LLVMAbstractState> callNode;
	protected Node<LLVMAbstractState> returnNode;
	protected LLVMAbstractState entryState;
	protected LLVMAbstractState callState;
	protected LLVMAbstractState returnState;

	protected LLVMAbstractState intersectedState;

	protected LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator;
	protected LLVMAllocationDeallocationEvaluator deallocationEvaluator;
	protected LLVMUnchangedMemoryRelationEvaluator unchangedEvaluator;
	

	protected Abortion aborter;
	
	protected LLVMImmutableFunctionGraph functionGraph;

	protected Set<LLVMSEPath> executionPaths;
	protected Set<LLVMSEPath> cycles;
	
	
	//LLVMHeuristicConstRef are mapped to themselves
	protected Map<LLVMSymbolicVariable,LLVMSymbolicVariable> returnStateVarToFreshVar;
	protected Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> callStateVarToReturnStateVars;
	protected Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> returnStateVarToCallStateVars;
	
	//contains those allocations of the call state and their former content for which we have not_deallocated, but not disjoint
	//@Deprecated
	//private Map<LLVMAllocation,Set<Pair<LLVMMemoryRange,LLVMMemoryInvariant>>> callStateMallocAllocationWithNotDeallocatedButNotDisjoint;
	
	/**
	 * Maps the indices of malloc allocations of the return state to their "new" index in the intersected state
	 */
	private Map<Integer, Integer> mallocAllocationIndicesReturnToIntersection;
	
	
	/** Maps stack allocations (topmost or lower stack frames) of the return state to allocations in the call state, or null, if no correspondence is known
	 * 
	 */
	private Map<LLVMAllocation, LLVMAllocation> renamingMapOfStackAllocationsReturnStateToCallState;

	
	private LLVMIntersectionHeuristics intersectionHeuristics;
	
	private String function;

    /**
     * TODO
     * 
     * @param callNode The call node.
     * @param returnNode The return state.
     * @return a pair (x,y), where y indicates whether the intersection result is identical to the previous result and x is the resulting intersected state
     * @throws IntersectionFailException If the intersection fails.
     */
    public LLVMIntersectionResult intersect(
    		LLVMSEGraph seGraph,
    		Node<LLVMAbstractState> entryNode,
    		Node<LLVMAbstractState> callNode,
    		Node<LLVMAbstractState> returnNode,
    		LLVMIntersectionResult previousResult,
			LLVMImmutableFunctionGraph functionGraph,
    		Abortion aborter)
    throws IntersectionFailException {
    	
    	//seGraph.dumpGraph();

    	if(functionGraph.isPathAgnostic()) {
    		LLVMSEPath sePath = new LLVMSEPath(functionGraph.getSingleExecutionPathViaMostGeneralEntryState(callNode, returnNode), seGraph);
    		executionPaths = Collections.singleton(sePath);
    		cycles = Collections.emptySet();
    		
    	} else {
    		executionPaths = functionGraph.getExecutionPathsViaMostGeneralEntryState(callNode,returnNode);
    		cycles = functionGraph.getAllCyclesReachableFromExecutionPaths(executionPaths);
    	}
    	
    	callState = callNode.getObject();
    	returnState = returnNode.getObject();
    	
    	this.aborter = aborter;
    	this.intersectionHeuristics = seGraph.getIntersectionHeuristics();
    	this.functionGraph = functionGraph;
    	this.function = functionGraph.getFunction();
    	this.module = seGraph.getModule();
    	
    	if(previousResult != null && Globals.useAssertions) {
    		assert callNode == previousResult.getCallNode();
    		assert returnNode == previousResult.getReturnNode();
    	}
	

    	initStructures(seGraph, entryNode, callNode, returnNode, executionPaths);
        
    	initRelationEvaluators();
    	
    	
    	
    	initIntersection(callState, returnState);
    	
    	
    	
    	
    	if(previousResult != null && yieldsIntersectionIdenticalTofPreviousResult(previousResult)) {
    		intersectedState = previousResult.getIntersectedState();
    		Node<LLVMAbstractState> intersectionNode = new Node<LLVMAbstractState>(intersectedState);
    		LLVMIntersectionResult res = new LLVMIntersectionResult(this,intersectionNode,previousResult,null);
    		return res;
    	}
    	
    	
		try {
			initFreshValues();
			
			handleReturnValue(aborter);

			intersectMemory(aborter);
			
			intersectIntegerKnowledge(aborter);

			if(intersectionHeuristics.useReturnStateRelationsWhenSummarizing(function)) {
				addEqualityInformationAccordingToVariableRenamings();
			}

			performPostProcessing();
		} catch (InconsistentStateException e) {
			throw new IntersectionFailException("Intersection failed due to inconsistent state");
		}
		Node<LLVMAbstractState> intersectionNode = new Node<LLVMAbstractState>(intersectedState);

		LLVMIntersectionResult res = new LLVMIntersectionResult(this,intersectionNode,null,null);
		return res;
    }
    
    
    protected void initFreshValues() {
    	//only have work to do in heuristic intersector
    }

    

    

    
    
    /**
     * Returns true iff the intersection we are currently building would yield the same as <code>previousResult</code>
     */
    //TODO FEM fix according to new things offered
    private boolean yieldsIntersectionIdenticalTofPreviousResult(LLVMIntersectionResult previousResult) {
    	if(previousResult == null)
    		return false;
    	
    	for(LLVMSymbolicVariable callStateVar : callState.getSymbolicVariables()) {
    		if(!renamingEvaluator.getReturnStateVariablesForCallStateVariable(callStateVar)
    			.equals(previousResult.getRenamingEvaluator().getReturnStateVariablesForCallStateVariable(callStateVar))) {
    			return false;
    		}
    			
    	}
    	
    	for(LLVMAllocation callStateAllocation : callState.getAllocations()) {
    		if(deallocationEvaluator.allocationLostDuringMergeWithoutDeallocationOnAllPaths(callStateAllocation)
    				!= previousResult.getAllocationDeallocationEvaluator().allocationLostDuringMergeWithoutDeallocationOnAllPaths(callStateAllocation)) {
    			return false;
    		}
    		if(!equalsNullOKForBoth(deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAllocation),
    				previousResult.getAllocationDeallocationEvaluator().allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAllocation))) {
    			return false;
    		}
    		if(deallocationEvaluator.allocationNotDeallocatedAndNotStoredToOnAllPaths(callStateAllocation) !=
    				previousResult.getAllocationDeallocationEvaluator().allocationNotDeallocatedAndNotStoredToOnAllPaths(callStateAllocation)) {
    			return false;
    		}
    		
    	}
    	
    	for(LLVMMemoryRange callStateMemRange : callState.getMemory().keySet()) {
    	    if (callStateMemRange instanceof LLVMMemoryRecursiveRange) {
    	        continue;
    	    }
    		if(unchangedEvaluator.unchanged(callStateMemRange) != previousResult.getUnchagedEvaluator().unchanged(callStateMemRange)) {
    			return false;
    		}
    		if(!equalsNullOKForBoth(unchangedEvaluator.turnedIntoReturnStateRangeOnAllPaths(callStateMemRange),
    				previousResult.getUnchagedEvaluator().turnedIntoReturnStateRangeOnAllPaths(callStateMemRange))) {
    			return false;
    		}
    	}
    	
    	return true;
    }
    
    

    
    Set<LLVMSymbolicVariable> getAllLLVMSymbolicVariable(IntegerRelation rel) {
    	Set<? extends IntegerVariable> ivars = rel.getVariables();
    	Set<LLVMSymbolicVariable> llvmVars = new LinkedHashSet<>();
    	for(IntegerVariable ivar : ivars) {
    		if(ivar instanceof LLVMSymbolicVariable)
    			llvmVars.add((LLVMSymbolicVariable) ivar);
    			
    	}
    	return llvmVars;
     }
    
    protected void initStructures(
    		LLVMSEGraph seGraph,
    		Node<LLVMAbstractState> entryNode,
    		Node<LLVMAbstractState> callNode,
    		Node<LLVMAbstractState> returnNode,
    		Set<LLVMSEPath> pathsFromCallToReturnNodeToRespect) {
    	this.module = seGraph.getModule();
    	this.entryNode = entryNode;
    	this.callNode = callNode;
    	this.returnNode = returnNode;

        
    }
    
    protected void initIntersection(LLVMAbstractState callState, LLVMAbstractState returnState) {
    	LLVMAbstractState resState = callState.setProgramPosition(returnState.getProgramPosition());
    	intersectedState = resState;
    }
    
    
	protected void handleReturnValue(Abortion aborter) {
		LLVMRetInstruction retIns = (LLVMRetInstruction) returnState.getCurrentInstruction();
		if (retIns.getReturnLiteral() instanceof LLVMVariableLiteral) {
			LLVMVariableLiteral returnedVariable = (LLVMVariableLiteral) retIns.getReturnLiteral();
			String varNameString = returnedVariable.getName();
			LLVMSimpleTerm resTerm = returnState.getSimpleTermForLiteral(retIns.getReturnLiteral());
			
			Map<LLVMSymbolicVariable, LLVMSymbolicVariable> variableMapReturnToIntersection = getReturnStateVarToFreshMap();
			
			if(resTerm instanceof LLVMSymbolicVariable) {
				LLVMSymbolicVariable correspondingSymbolicVariableOfIntersection = variableMapReturnToIntersection.get(resTerm);
				LLVMType returnType = returnState.getProgramVariables().get(varNameString).y;
				intersectedState = intersectedState.setProgramVariable(varNameString, correspondingSymbolicVariableOfIntersection, returnType);
			}
			
		}

	}
	

	

	

	
	protected Map<LLVMSymbolicVariable,LLVMSymbolicVariable> getReturnStateVarToFreshMap() {
		if(returnStateVarToFreshVar == null) {
			returnStateVarToFreshVar = new LinkedHashMap<>();
			
			for(LLVMSymbolicVariable returnStateVar : returnState.getSymbolicVariables()) {
				if(returnStateVar instanceof LLVMHeuristicConstRef) {
					returnStateVarToFreshVar.put(returnStateVar, returnStateVar);
				} else {
					returnStateVarToFreshVar.put(returnStateVar, getTermFactory().freshVariable());
				}
			}
		}
		return returnStateVarToFreshVar;
	}
	
	protected Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> getCallStateVarToReturnStateVarsMap() {
		if(callStateVarToReturnStateVars == null) {
			callStateVarToReturnStateVars = new LinkedHashMap<>();
			for(LLVMSymbolicVariable callStateVar : callState.getSymbolicVariables()) {
				callStateVarToReturnStateVars.put(callStateVar,
						renamingEvaluator.getReturnStateVariablesForCallStateVariable(callStateVar));
			}
		}
		return callStateVarToReturnStateVars;
	}
	
	protected Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> getReturnStateVarToCallStateVarsMap() {
		if(returnStateVarToCallStateVars == null) {
			returnStateVarToCallStateVars = new LinkedHashMap<>();
			for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> entry : callStateVarToReturnStateVars.entrySet()) {
				for(LLVMSymbolicVariable returnStateVar : entry.getValue()) {
					Set<LLVMSymbolicVariable> callStateVarsForReturnStateVar = 
							returnStateVarToCallStateVars.computeIfAbsent(returnStateVar, v -> new LinkedHashSet<>());
					
					callStateVarsForReturnStateVar.add(entry.getKey());
				}
			}
		}
		return returnStateVarToCallStateVars;
	}
	
	
	


	
	
	protected void intersectMemory(Abortion aborter) {
		intersectAllocations(aborter);
    	
    	intersectHeap(aborter);
    	
    	intersectedState = intersectedState.cleanHeapEntriesWithoutAllocation(aborter);
	}
	
	
	
	

    protected void intersectAllocations(Abortion aborter) {
    	removeNonPreserverdAllocationsFromIntersecion(aborter);
    	
    	String bottomMostFunction = callState.getBottommostFunctionInStack();
    	if(intersectionHeuristics.trackAllocationModificationInStateForFunction(bottomMostFunction)) {
    		updateChangeFlagsCallStateAllocations();
    	}
    	
    	if(intersectionHeuristics.useReturnStateAllocationsWhenSummarizing(function)) {
    		addRenamedReturnStateMallocAllocationsToIntersection(aborter);
    	}
    	
    	
    }
    
    private void updateChangeFlagsCallStateAllocations() {
    	Map<Integer,Boolean> mutableMap = new LinkedHashMap<>(intersectedState.getAllocationChangedSinceEntryStateMap());
    	for(int intersectionAllocationIndex = 0; intersectionAllocationIndex < intersectedState.getAllocations().size(); intersectionAllocationIndex++) {
    		if(mutableMap.containsKey(intersectionAllocationIndex)) {
	    		LLVMAllocation alloc = intersectedState.getAllocations().get(intersectionAllocationIndex);
	    		
	    		//at this point, all allocations of the intersection are also allocations of the call state
	    		if(!mutableMap.get(intersectionAllocationIndex) && !deallocationEvaluator.allocationNotDeallocatedAndNotStoredToOnAllPaths(alloc)) {
	    			mutableMap.put(intersectionAllocationIndex, true);
	    		}
    		}
    	}
    	intersectedState = intersectedState.setAllocationChangedSinceEntryState(ImmutableCreator.create(mutableMap));
    }
    
    private int getAllocationIndexForIntersectionIndexCorrespondingToReturnStateAllocation(int returnStateAllocationIndex, Abortion aborter) {
    	if(mallocAllocationIndicesReturnToIntersection == null)
			throw new IllegalStateException("Must create index mapping first!");
    	
    	LLVMAllocation returnStateAllocation = returnState.getAllocations().get(returnStateAllocationIndex); 
    	if(returnState.getAllocatedByMalloc().contains(returnStateAllocation)) {
    		return mallocAllocationIndicesReturnToIntersection.get(returnStateAllocationIndex);
    	} else {
    		LLVMAllocation callStateAllocation = getRenamingMapOfStackAllocationsReturnStateToCallState(aborter).get(returnStateAllocation);
    		if(callStateAllocation == null) {
    			return -1;
    		}
    		
    		return getIndexForAllocation(intersectedState,callStateAllocation);
    	}
    }
    
    private Map<LLVMAllocation, LLVMAllocation> getRenamingMapOfStackAllocationsReturnStateToCallState(Abortion aborter) {
    	if(renamingMapOfStackAllocationsReturnStateToCallState == null) {
    		renamingMapOfStackAllocationsReturnStateToCallState = new LinkedHashMap<>();
    		
    		List<LLVMAllocation> returnStateStackAllocations = new ArrayList<>(returnState.getAllocations());
    		returnStateStackAllocations.removeAll(returnState.getAllocatedByMalloc());
    		
    		List<LLVMAllocation> callStateStackAllocations = new ArrayList<>(callState.getAllocations());
    		callStateStackAllocations.removeAll(callState.getAllocatedByMalloc());
    		
    			for(LLVMAllocation callStateAllocation : callStateStackAllocations) {
    				if(!(callStateAllocation.x instanceof LLVMSymbolicVariable)
    						|| !(callStateAllocation.y instanceof LLVMSymbolicVariable)) {
    					throw new IllegalStateException("Cannot handle allocation with non symbolic variable bounds");
    				}
    				
    				LLVMAllocation returnStateAlloc = 
    						deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAllocation);
    				
    				if(returnStateAlloc != null) {
    					renamingMapOfStackAllocationsReturnStateToCallState.put(returnStateAlloc, callStateAllocation);
    				} else {
    				
					LLVMSymbolicVariable lowerCallAllocBound = (LLVMSymbolicVariable) callStateAllocation.x;
					LLVMSymbolicVariable upperCallAllocBound = (LLVMSymbolicVariable) callStateAllocation.y;

					Set<LLVMSymbolicVariable> retStateLowerVarRenaming = renamingEvaluator
							.getReturnStateVariablesForCallStateVariable(lowerCallAllocBound);
					Set<LLVMSymbolicVariable> retStateUpperVarRenaming = renamingEvaluator
							.getReturnStateVariablesForCallStateVariable(upperCallAllocBound);

					for (LLVMSymbolicVariable newLower : retStateLowerVarRenaming) {
						for (LLVMSymbolicVariable newUpper : retStateUpperVarRenaming) {
							LLVMAllocation renamedAlloc = new LLVMAllocation(newLower, newUpper);
							// TODO FEM check if this actually triggers
							// sometimes
							if (returnStateStackAllocations.contains(renamedAlloc)) {
								renamingMapOfStackAllocationsReturnStateToCallState.put(renamedAlloc,
										callStateAllocation);
							}
						}
					}

				}

			}
    		
    	}
    	return renamingMapOfStackAllocationsReturnStateToCallState;
    }
    
    
    private static int getIndexForAllocation(LLVMAbstractState state, LLVMAllocation allocation) {
    	for(int index = 0; index < state.getAllocations().size(); index++) {
    		if(state.getAllocations().get(index).equals(allocation))
    			return index;
    	}
    	throw new IllegalArgumentException("The given allocation was not found in the allocations of the state");
    }
    

    

	//must be called before adding allocations from return state
    private void removeNonPreserverdAllocationsFromIntersecion(Abortion aborter) {
    	if(Globals.useAssertions) {
    		assert callState.getAllocations().equals(intersectedState.getAllocations());
    	}
    	
		boolean continueOuter = true;
		//TODO FEM this double loop is uncessearily inefficient
		outerLoop:
		while (continueOuter) {
			continueOuter = false;
			Set<LLVMAllocation> callStateMallocAllocations = callState.getAllocatedByMalloc();
			
			List<LLVMAllocation> intersectionAllocations = intersectedState.getAllocations();
			
			for (int allocIndex = 0; allocIndex < intersectionAllocations.size(); allocIndex++) {
				LLVMAllocation intersectionAllocation = intersectedState.getAllocations().get(allocIndex);
				if (callStateMallocAllocations.contains(intersectionAllocation)) {
					
					
					boolean turnsIntoReturnStateAllocation = deallocationEvaluator.
							allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(intersectionAllocation) != null;
					
					boolean isLostOnPaths = deallocationEvaluator.allocationLostDuringMergeWithoutDeallocationOnAllPaths(intersectionAllocation);
					

					boolean mustFree = !(turnsIntoReturnStateAllocation || isLostOnPaths);
					
					if(mustFree) {						
						try {
							intersectedState = intersectedState.freeAllocation(allocIndex, -1, aborter);
							continueOuter = true;
							continue outerLoop;
						} catch (InvalidFreeException e) {
							throw new IllegalStateException("Memory Errors should have been caught during earlier evaluation");
						}
					}
					
				} else {
					if(Globals.useAssertions) {
						assert !intersectedState.getAllocatedByMalloc().contains(intersectionAllocation) :
							"Got malloc allocation in intersection with no matching malloc allocation of call state." +
							"This Should not be possible at this point";
					}
				}
			}

		}
    }
    
    Map<LLVMAllocation,LLVMAllocation> getCallStateToReturnStateAllocationMap() {
    	//TODO cache this
    	
    	Map<LLVMAllocation,LLVMAllocation> result = new LinkedHashMap<>();
    	
    	for(LLVMAllocation callStateAlloc : callState.getAllocations()) {
    		LLVMAllocation returnStateAlloc = deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAlloc);
    		if(returnStateAlloc != null) {
    			if(Globals.useAssertions) {
    				assert result.get(callStateAlloc) == null : "One call state allocation became two in return state?";
    			}
    			result.put(callStateAlloc,returnStateAlloc);
    			
    		}
    	}
    	
    	return result;
    }
    
    
    Map<LLVMAllocation,LLVMAllocation> getReturnStateToCallStateAllocationMap() {
    	//TODO cache this
    	
    	Map<LLVMAllocation,LLVMAllocation> result = new LinkedHashMap<>();
    	
    	for(LLVMAllocation callStateAlloc : callState.getAllocations()) {
    		LLVMAllocation returnStateAlloc = deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAlloc);
    		if(returnStateAlloc != null) {
    			if(Globals.useAssertions) {
    				assert result.get(returnStateAlloc) == null : "Two allocations from call state became one in return state?";
    			}
    			result.put(returnStateAlloc,callStateAlloc);
    			
    		}
    	}
    	
    	return result;
    }
    
    Map<LLVMMemoryRange,LLVMMemoryRange> getReturnStateToCallStateMemoryRangeMap() {
    	Map<LLVMMemoryRange,LLVMMemoryRange> result = new LinkedHashMap<>();
    	
    	for(LLVMMemoryRange callStateRange : callState.getMemory().keySet()) {
    	    if (callStateRange instanceof LLVMMemoryRecursiveRange) {
    	        continue;
    	    }
    		LLVMMemoryRange returnStateRange = unchangedEvaluator.turnedIntoReturnStateRangeOnAllPaths(callStateRange);
    		if(returnStateRange != null) {
    			if(Globals.useAssertions) {
    				assert result.get(returnStateRange) == null : "Two memory ranges from return state are one in call state?";
    			}
    			result.put(returnStateRange,callStateRange);
    		}
    	}
    	
    	return result;
    }
    
    
    private void addRenamedReturnStateMallocAllocationsToIntersection(Abortion aborter) {
    	mallocAllocationIndicesReturnToIntersection = new LinkedHashMap<>();
    	List<LLVMAllocation> returnStateAllocations = returnState.getAllocations();
    	
    	Map<LLVMAllocation,LLVMAllocation> returnStateToCallStateAllocations = getReturnStateToCallStateAllocationMap();
    	Map<Integer,Boolean> changedAllocationFlags = intersectedState.getAllocationChangedSinceEntryStateMap();
    	Map<Integer,Boolean> returnStateChangeFlagMap = returnState.getAllocationChangedSinceEntryStateMap();
    	String bottomMostFunction = callState.getBottommostFunctionInStack();
    	if(intersectionHeuristics.trackAllocationModificationInStateForFunction(bottomMostFunction)) {
    		changedAllocationFlags = new LinkedHashMap<>(intersectedState.getAllocationChangedSinceEntryStateMap());
    	}
    	
    	
    	for(Integer returnStateMallocAllocationIndex : returnState.getAllocatedByMallocIndices()) {
    		
    		LLVMAllocation returnStateMallocAllocation = returnStateAllocations.get(returnStateMallocAllocationIndex);
    		
    		if(returnStateToCallStateAllocations.containsKey(returnStateMallocAllocation)) {
    			if(Globals.useAssertions) {
    				assert intersectedState.getAllocatedByMalloc().contains(returnStateToCallStateAllocations.get(returnStateMallocAllocation));
    			}
    			
    			//Do not add this one, we still have it from the call state.
    			//But store the mapping
    			LLVMAllocation callStateAllocation = returnStateToCallStateAllocations.get(returnStateMallocAllocation);
    			int intersectionAllocIndex = intersectedState.getAllocations().indexOf(callStateAllocation);
    			if(intersectionAllocIndex == -1) {
    				throw new IllegalStateException("Map said we have a corresponding call/intersected state allocation, but we did not find it");
    			}
    			mallocAllocationIndicesReturnToIntersection.put(returnStateMallocAllocationIndex, intersectionAllocIndex);
    		} else {
				// If the return state malloc allocation has no equivalent from
				// the call state, we add it to the intersection using fresh
				// names
				if (!(returnStateMallocAllocation.x instanceof LLVMSymbolicVariable
						&& returnStateMallocAllocation.y instanceof LLVMSymbolicVariable))
					throw new IllegalStateException("Got allocation with constant bounds");
				LLVMSymbolicVariable lower = (LLVMSymbolicVariable) returnStateMallocAllocation.x;
				LLVMSymbolicVariable upper = (LLVMSymbolicVariable) returnStateMallocAllocation.y;

				LLVMSymbolicVariable lowerWithIntersectionName = (LLVMSymbolicVariable) lower
						.applySubstitution(getReturnStateVarToFreshMap());
				LLVMSymbolicVariable upperWithIntersectionName = (LLVMSymbolicVariable) upper
						.applySubstitution(getReturnStateVarToFreshMap());

				int intersectionAllocIndex = intersectedState.getAllocations().size();
				intersectedState = intersectedState.allocateMemoryAndAssociatePointer(lowerWithIntersectionName,
						upperWithIntersectionName, null, null, false, null, aborter);

				mallocAllocationIndicesReturnToIntersection.put(returnStateMallocAllocationIndex,
						intersectionAllocIndex);
				
		    	if(intersectionHeuristics.trackAllocationModificationInStateForFunction(bottomMostFunction)) {
		    		if(returnStateChangeFlagMap != null) {
		    			Boolean result = returnStateChangeFlagMap.get(returnStateMallocAllocationIndex);
		    			if(result != null) {
		    				changedAllocationFlags.put(intersectionAllocIndex, result);
		    			}
		    		}
		    	}
    		}
    	}
    	if(changedAllocationFlags != null) {
    		intersectedState = intersectedState.setAllocationChangedSinceEntryState(ImmutableCreator.create(changedAllocationFlags));
    	}
    	
    			
    }
    
    
    
    protected void intersectHeap(Abortion aborter) {
    	removePotentiallyInvalidatedCallStateHeapInformationFromIntersection();

    	if(intersectionHeuristics.useReturnStateHeapEntriesWhenSummarizing(function)) {
    		addRenamedReturnStateHeapInfoToIntersection(aborter);
    	}
    }
    

    

	//must not add return state heap entries to intersection beforehand
	//must remove heap entries for possibly deallocated call state malloc allocations beforehand
    private void removePotentiallyInvalidatedCallStateHeapInformationFromIntersection() {
    	Set<LLVMMemoryRange> heapRangesToRemoveAccess = new LinkedHashSet<>(intersectedState.getMemory().keySet());
    	
    	
    	Iterator<LLVMMemoryRange> it = heapRangesToRemoveAccess.iterator();
    	while(it.hasNext()) {
    		LLVMMemoryRange range = it.next();
    		boolean unchanged = unchangedEvaluator.unchanged(range);
    		if(unchanged) {
    			//remove from set whose entries will be removed from intersection
    			it.remove();
    		}
    	}
    	
        int instructionCount = module.getAllPositions().size();
        if(instructionCount < Globals.INSTRUCTION_COUNT_THRESHOLD) {
            intersectedState = intersectedState.removeHeapAccesses(heapRangesToRemoveAccess);
    	}

    }
    
    /*private boolean notModifiedOnAnyPath(LLVMMemoryRange callStateRange, Abortion aborter) {
    	return unchangedEvaluator.unchangedOld(callStateRange);
    }*/
    
    private void addRenamedReturnStateHeapInfoToIntersection(Abortion aborter) {
    	Map<LLVMMemoryRange, LLVMMemoryInvariant> returnStateMemory = returnState.getMemory();
    	Map<LLVMSymbolicVariable, LLVMSymbolicVariable> variableMappingFromReturnToIntersectedState = getReturnStateVarToFreshMap();
    	
    	Map<LLVMMemoryRange,LLVMMemoryRange> returnStateToCallStateRangeMap = getReturnStateToCallStateMemoryRangeMap();
    	
    	
    	for(Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> returnStateMemoryEntry : returnStateMemory.entrySet()) {
    		
    		
    		
    		LLVMMemoryRange returnStateMemoryRange = returnStateMemoryEntry.getKey();
    		
    		if(returnStateToCallStateRangeMap.containsKey(returnStateMemoryRange)) {
    			//Do not add, because it survived from the call state
    			continue;
    		}
    		
    		LLVMPointerType pointerType = new LLVMPointerType(returnStateMemoryRange.getType(), module.getPointerSize(), null);
    		Pair<LLVMAssociationIndex, LLVMAbstractState> returnStateIndexPair 
				= returnState.getAssociatedAllocationIndex(returnStateMemoryRange, aborter);		
    		if(returnStateIndexPair.x == null && !(returnStateMemoryRange instanceof LLVMMemoryRecursiveRange)) {
    			if(Globals.DEBUG_FEMRICH)
    				System.err.println("Heap entry " + returnStateMemoryEntry + " did not have a corresponding allocation in return state " + returnNode.getNodeNumber());
    			continue;
    		}
    		int returnStateAllocIndex = -1;
    		if (!(returnStateMemoryRange instanceof LLVMMemoryRecursiveRange)) {
                returnStateAllocIndex = returnStateIndexPair.x.x;
    		}
    		
    		
    		LLVMSimpleTerm renamedFromRef = 
    				(LLVMSimpleTerm) returnStateMemoryRange.getFromRef().applySubstitution(variableMappingFromReturnToIntersectedState);
    		LLVMSimpleTerm renamedToRef = 
    				(LLVMSimpleTerm) returnStateMemoryRange.getToRef().applySubstitution(variableMappingFromReturnToIntersectedState);
            LLVMMemoryRange renamedRange;
            if (returnStateMemoryRange instanceof LLVMMemoryRecursiveRange) {
                LLVMSimpleTerm length =
                    (LLVMSimpleTerm) ((LLVMMemoryRecursiveRange)returnStateMemoryRange).getLength().applySubstitution(variableMappingFromReturnToIntersectedState);
                renamedRange = new LLVMMemoryRecursiveRange(renamedFromRef, renamedToRef, returnStateMemoryEntry.getKey().getType(), length);
            } else {
                renamedRange = new LLVMMemoryRange(renamedFromRef, renamedToRef, returnStateMemoryEntry.getKey().getType(), returnStateMemoryEntry.getKey().getUnsigned());
            }
    		
    		LLVMMemoryInvariant returnStateMemoryInvariant = returnStateMemoryEntry.getValue();
    		LLVMMemoryInvariant renamedMemoryInvariant = returnStateMemoryInvariant.replaceReferences(variableMappingFromReturnToIntersectedState);
    		
    	
    		
    		
    		int intersectionIndex = -1;
            if (!(returnStateMemoryRange instanceof LLVMMemoryRecursiveRange)) {
    		    intersectionIndex = getAllocationIndexForIntersectionIndexCorrespondingToReturnStateAllocation(returnStateAllocIndex, aborter);
                if(intersectionIndex == -1) {
                    //System.err.println("Did not find matching allocation for return node  " + this.returnNode.getNodeNumber() + " memory range " + returnStateMemoryRange );
                    continue;
                }
            }
    		
    		intersectedState = intersectedState.setHeapEntry(renamedRange, renamedMemoryInvariant);
    		
    		if(!( renamedFromRef instanceof LLVMSymbolicVariable))
    				throw new IllegalStateException("Renamed Lower bound of current allocation was not a symbolic variable");

            if (!(returnStateMemoryRange instanceof LLVMMemoryRecursiveRange)) {
    		    intersectedState 
    			    = intersectedState.associateAccess((LLVMSymbolicVariable) renamedFromRef,pointerType, intersectionIndex, null, aborter);
            }
    	}
    }
    

    

    
    
    protected void intersectIntegerKnowledge(Abortion aborter) throws IntersectionFailException {
    	/*

    	NEW IDEAS:

    	keep in mind that we must manually add equality constraints afterwards


    	 */


    	if(intersectionHeuristics.useReturnStateRelationsWhenSummarizing(function)) {
			Set<LLVMRelation> relationsToAdd = new LinkedHashSet<>();
			Set<IntegerRelation> relationsOfReturnState = getAllRelationsOfState(returnState);
			
			for (IntegerRelation rel : relationsOfReturnState) {
				IntegerRelation substitutedRelation = rel.applySubstitution(getReturnStateVarToFreshMap());
				LLVMRelation substitutedLLVMRelation = getRelationFactory().createRelation(substitutedRelation);

				relationsToAdd.add(substitutedLLVMRelation);
			}
    	
    	
    	//If some variable v was renamed to a constant, we can use that information
    	/*Map<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> renamingsFromCallToReturn = getRenamingsFromCallToReturnState(aborter);
    	for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> entry : renamingsFromCallToReturn.entrySet()) {
    		for(LLVMSymbolicVariable renaming : entry.getValue()) {
    			if(renaming instanceof LLVMHeuristicConstRef) {
    				LLVMTermFactory tf = getRelationFactory().getTermFactory();
    				LLVMHeuristicConstRef constRenaming = (LLVMHeuristicConstRef) renaming;
    				LLVMRelation valueRelation = getRelationFactory().equalTo(entry.getKey(), tf.constant(constRenaming.getIntegerValue()));
    				
    				relationsToAdd.add(valueRelation);
    			}
    		}
    	}*/
    	
			addRelationsToIntersection(relationsToAdd, aborter);

			
    	}
    	
    }
    
    
	protected void addEqualityInformationAccordingToVariableRenamings() throws IntersectionFailException {
    	Set<LLVMRelation> equalitiesToAdd = new LinkedHashSet<>();
    	Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> callToRetVars = getCallStateVarToReturnStateVarsMap();
    	
    	Map<LLVMSymbolicVariable,LLVMSymbolicVariable> retVarToFresh = getReturnStateVarToFreshMap();
    	
    	for(Map.Entry<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> e : callToRetVars.entrySet()) {
    		for(LLVMSymbolicVariable retVar : e.getValue()) {
    		LLVMRelation eq = getRelationFactory().equalTo(e.getKey(),retVarToFresh.get(retVar));
    		}
    	}
    	
    	//contradictions are detected here:
    	addRelationsToIntersection(equalitiesToAdd,aborter);
    	
    }
	
	protected void performPostProcessing() {
		intersectedState = intersectedState.postProcessAfterIntersection(false, aborter).x;
		createEntryStateVarMapIfNecessary();
	}
    
    protected void addRelationsToIntersection(Set<LLVMRelation> relations, Abortion aborter) throws IntersectionFailException {
    	for(LLVMRelation rel : relations) {
    		if(intersectedState.checkRelation(rel.negate(), aborter).x) {
    			throw new IntersectionFailException("Inconsistent Knowledge");
    		}
    		intersectedState = intersectedState.addRelation(rel, aborter);
    	}
    }
    
    protected Set<IntegerRelation> getAllRelationsOfState(LLVMAbstractState state) {
    	//TODO FEM right now, this adds much more than the knowledge base. ok?
    	return state.getIntegerState().toRelationSet();
    }
    

    /**
     * @return The factory to build relations.
     */
    protected LLVMRelationFactory getRelationFactory() {
        return LLVMDefaultRelationFactory.LLVM_DEFAULT_RELATION_FACTORY;
    }
    
    /*protected Abortion getAborter() {
    	return this.seGraph.getStrategyParameters().aborter;
    }*/

    private void initRelationEvaluators() {
    	Triple<LLVMSymbolicVariableRenamingRelationEvaluator, 
    		LLVMAllocationDeallocationEvaluator,
    		LLVMUnchangedMemoryRelationEvaluator> evaluators = intersectionHeuristics.createEvaluators(callNode, returnNode, executionPaths, functionGraph,module, getRelationFactory(), aborter);
    	
    	renamingEvaluator = evaluators.x;
		deallocationEvaluator = evaluators.y;
		unchangedEvaluator = evaluators.z;
	}

	public Set<LLVMSEPath> getExecutionPaths() {
    	return executionPaths;
	}


	public Node<LLVMAbstractState> getReturnNode() {
		return returnNode;
	}

	public Node<LLVMAbstractState> getCallNode() {
		return callNode;
	}

	public Set<LLVMSEPath> getRespectedCycles() {
		return cycles;
	}

	LLVMSymbolicVariableRenamingRelationEvaluator getRenamingEvaluator() {
		return renamingEvaluator;
	}


	LLVMAllocationDeallocationEvaluator getDeallocationEvaluator() {
		return deallocationEvaluator;
	}

	LLVMUnchangedMemoryRelationEvaluator getUnchangedEvaluator() {
		return unchangedEvaluator;
	}
	
	LLVMTermFactory getTermFactory() {
		return getRelationFactory().getTermFactory();
	}
	
	//do not call unless intersection process is finished
	public Set<LLVMSymbolicVariable> getIntersectionNamesForVariable(LLVMSymbolicVariable callStateVariable) {
		Set<LLVMSymbolicVariable> intersectionVars = getCallStateVarToReturnStateVarsMap().get(callStateVariable)
				.stream()
				.map(retVar -> getReturnStateVarToFreshMap().get(retVar))
				.collect(Collectors.toCollection(LinkedHashSet::new));
		if(intersectedState.getSymbolicVariables().contains(callStateVariable)) {
			intersectionVars.add(callStateVariable);
		}
		return intersectionVars;
		
	}
	

  //do not call unless intersection process is finished
	public LLVMAllocation getNotDeallocatedIntersectedStateAllocation(LLVMAllocation callStateAllocation) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getAllocations().contains(callStateAllocation);
		}
		
		//may be null
		LLVMAllocation returnStateAllocation = deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAllocation);
		if(returnStateAllocation == null) {
			if(deallocationEvaluator.allocationLostDuringMergeWithoutDeallocationOnAllPaths(callStateAllocation)) {
				return handleAllocationRenaming(callStateAllocation, true);
			} else {
				return null;
			}
		} else {
			return handleAllocationRenaming(returnStateAllocation, false);
			
		}
	}
    
    protected LLVMAllocation handleAllocationRenaming(LLVMAllocation allocation, boolean fromCallState) {
    	Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> allocVars = LLVMAllocationDeallocationEvaluator.getVariablesFromAllocation(allocation);
		
		LLVMSimpleTerm lowerBoundRenaming = null;
		if(allocVars.x == null) {
			lowerBoundRenaming = allocation.x; //must have been a constant
		} else {
			if(fromCallState) {
				lowerBoundRenaming = allocVars.x;
			} else {
				lowerBoundRenaming = getReturnStateVarToFreshMap().get(allocVars.x);
			}
		}
		
		LLVMSimpleTerm upperBoundRenaming = null;
		if(allocVars.y == null) {
			upperBoundRenaming = allocation.y; //must have been a constant
		} else {
			if(fromCallState) {
				upperBoundRenaming = allocVars.y;
			} else {
				upperBoundRenaming = getReturnStateVarToFreshMap().get(allocVars.y);
			}
		}

		
		LLVMAllocation retStateAllocationWithIntersectionNames = new LLVMAllocation(lowerBoundRenaming, upperBoundRenaming);
		if(!intersectedState.getAllocations().contains(retStateAllocationWithIntersectionNames)) {
			throw new IllegalStateException();
		}
		return retStateAllocationWithIntersectionNames;
    }
	
	
	//do not call unless intersection process is finished
	public boolean allocationUnchanged(LLVMAllocation callStateAllocation) {
		return deallocationEvaluator.allocationNotDeallocatedAndNotStoredToOnAllPaths(callStateAllocation);
	}
	
	//do not call unless intersection process is finished
	public LLVMMemoryRange getUnchangedIntersectedStateMemoryRange(LLVMMemoryRange callStateMemoryRange) {
		LLVMMemoryRange returnStateRange = unchangedEvaluator.turnedIntoReturnStateRangeOnAllPaths(callStateMemoryRange);
		
		if(returnStateRange == null) {
			return null;
		} else {
			Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> rangeVars = LLVMUnchangedMemoryRelationEvaluator.getVariablesFromRange(returnStateRange);
			
			LLVMSimpleTerm lowerBoundRenaming = rangeVars.x == null ? callStateMemoryRange.getFromRef() :
				getReturnStateVarToFreshMap().get(rangeVars.x);
			
			LLVMSimpleTerm upperBoundRenaming = rangeVars.y == null ? callStateMemoryRange.getToRef() :
				getReturnStateVarToFreshMap().get(rangeVars.y);
			
			LLVMMemoryRange renamedIntersectionRange = new LLVMMemoryRange(lowerBoundRenaming, upperBoundRenaming, callStateMemoryRange.getType(), callStateMemoryRange.getUnsigned());
			
			if(!intersectedState.getMemory().containsKey(renamedIntersectionRange)) {
				throw new IllegalStateException();
			}
			
			return renamedIntersectionRange;
		}
	}
	
	//should be the last thing we do during intersection
	protected void createEntryStateVarMapIfNecessary() {
		if(callState.getEntryStateVarCorrespondenceMap() != null) {
			intersectedState = LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.handleCallStateToIntersectionEntryStateVarMap(this, intersectedState);
		}
	}
	
	private static <T> boolean equalsNullOKForBoth(T o1, T o2) {
		if(o1 == null && o2 == null) {
			return true;
		}
		if(o1 == null || o2 == null) {
			return false; // the other one is not null!
		}
		return o1.equals(o2);
		
	}
}
