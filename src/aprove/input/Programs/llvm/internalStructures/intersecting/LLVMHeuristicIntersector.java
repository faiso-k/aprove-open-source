package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.math.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.GlobalSettings;
import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Variant of the LLVMIntersector for heuristic states.
 * @author Frank Emrich, cryingshadow
 * @version $Id$
 */
public class LLVMHeuristicIntersector extends LLVMIntersector {

	protected Map<LLVMSymbolicVariable,LLVMSymbolicVariable> replacements;
	
    @Override
    protected LLVMHeuristicRelationFactory getRelationFactory() {
        return LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
    }
    
	/*@Override
	protected void createVariableMappingFromReturnToIntersectedState(Abortion aborter) {
		boolean wasNull = intermediateResult.variableMappingFromReturnToIntersectedState == null;
		super.createVariableMappingFromReturnToIntersectedState(aborter);
		//TODO Frank: Check if this can (or should) avoided
		if (wasNull) {
			for (LLVMSymbolicVariable var : intermediateResult.variableMappingFromReturnToIntersectedState.values()) {
				LLVMHeuristicVariable hVar = (LLVMHeuristicVariable) var;

				//LLVMHeuristicState intersection = ((LLVMHeuristicState) intermediateResult.intersectedState);

				initValueInIntersectionIfNotPresent(hVar);
				
			}
		}
	}*/
    
    protected void initFreshValues() {
    	//only have work to do in heuristic intersector
    	LLVMHeuristicState heuristicRetState = ((LLVMHeuristicState) returnState);
    	
    	Map<LLVMSymbolicVariable,LLVMSymbolicVariable> retToFresh = getReturnStateVarToFreshMap();
    	for(Map.Entry<LLVMSymbolicVariable,LLVMSymbolicVariable> e : retToFresh.entrySet()) {
    		LLVMHeuristicState heuristicIntersection = ((LLVMHeuristicState) intersectedState);
    		
    		LLVMHeuristicVariable heuristicRetVar = (LLVMHeuristicVariable) e.getKey();
    		
    		if(heuristicRetVar instanceof LLVMHeuristicConstRef)
    			continue; //no need to init const values
    		
    		LLVMValue retValue = heuristicRetState.getValue(heuristicRetVar);
    		
    		LLVMHeuristicVariable heuristicIntVar = (LLVMHeuristicVariable) retToFresh.get(heuristicRetVar);
    		
    		if(heuristicIntersection.getValue(heuristicIntVar) != null) {
    			throw new IllegalStateException("Variable that is supposed to be fresh already has a value?");
    		}
    		
    		intersectedState = heuristicIntersection.setValue(heuristicIntVar, retValue);
    		
    	}
    	
    	
    }
    
    
    protected void addEqualityInformationAccordingToVariableRenamings() throws IntersectionFailException { 	
    	replacements = new LinkedHashMap<>();
    	

    	Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> callToRetVars = getCallStateVarToReturnStateVarsMap();
    	Map<LLVMSymbolicVariable,LLVMSymbolicVariable> retToFresh = getReturnStateVarToFreshMap();
    	
    	callStateVarLoop:
    	for(Map.Entry<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> e : callToRetVars.entrySet()) {		
    		for(LLVMSymbolicVariable retVar : e.getValue()) {
    			LLVMHeuristicState  heuristicIntersection = ((LLVMHeuristicState) intersectedState);
    			
    			LLVMSymbolicVariable callStateVar = e.getKey();
    			LLVMSymbolicVariable renamingOfCallStateVar = transitiveClosureOfMap(replacements,callStateVar);
    			boolean callVarLost = false;
    			
    			renamingOfCallStateVar =  renamingOfCallStateVar == null ? callStateVar : renamingOfCallStateVar;
    			if(!intersectedState.getSymbolicVariables().contains(renamingOfCallStateVar)) {
    				if(Globals.DEBUG_FEMRICH) {
    					System.err.println("Lost call state var: " + callStateVar);
    				}
    				callVarLost = true;
    				continue callStateVarLoop;
    			}
    			
    			LLVMSymbolicVariable retVarFresh = retToFresh.get(retVar);
    			LLVMSymbolicVariable renamingOfReturnStateVar = transitiveClosureOfMap(replacements,retVarFresh);
    			
    			renamingOfReturnStateVar =  renamingOfReturnStateVar == null ? retVarFresh : renamingOfReturnStateVar;
    			if(!intersectedState.getSymbolicVariables().contains(renamingOfReturnStateVar)) {
    				continue;
    				//throw new IllegalStateException("Lost return state var");
    			}
    			
    			if(callVarLost) {
    				//This may happen for example if the call state var was for a heap entry that was removed during intersection
    				//and the call state var was not used elsewhere in the state
    				//we cannot unify the variables, but at least we can manually intersect their values
    				intersectValuesForLostCallStateVar(callStateVar,renamingOfReturnStateVar);
    				
    			} else {
	    			//Let's check if unifying the variables yields a contradiction:
	    			LLVMRelation notEqRel = getRelationFactory().notEqualTo(renamingOfReturnStateVar,renamingOfCallStateVar);
	    			if(intersectedState.checkRelation(notEqRel, aborter).x) {
	        			throw new IntersectionFailException("Inconsistent Knowledge");
	        		}
	    			
	    			LLVMReplacementResult replacementResult = heuristicIntersection.unifySymbolicVariables((LLVMHeuristicVariable)renamingOfReturnStateVar,(LLVMHeuristicVariable) renamingOfCallStateVar);
	    			intersectedState = replacementResult.x.cleanRelations(aborter);
	    			for(Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> repE : replacementResult.y.entrySet()) {
	    				if(repE.getKey() instanceof LLVMHeuristicConstRef && repE.getValue() instanceof LLVMHeuristicConstRef && repE.getKey().equals(repE.getValue())) {
	    					continue;
	    				}
	    				
	    				if(replacements.containsKey(repE.getKey())) {
	    					throw new IllegalStateException("Changed existing replacement");
	    				} else {
	    					replacements.put(repE.getKey(),repE.getValue());
	    				}
	    			}
    			}
    			
    			
    		}
    		
    	}
    	
    	/*for(Map.Entry<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> e : callToRetVars.entrySet()) {
    		if(!e.getValue().isEmpty() && !intersectedState.getSymbolicVariables().contains(e.getKey()) && e.getValue().stream().allMatch(v -> !(v instanceof LLVMHeuristicConstRef))) {
    			throw new IllegalStateException("Lost call state variable");
    		} 
    	}*/
    }
    
    private void intersectValuesForLostCallStateVar(LLVMSymbolicVariable callStateVar, LLVMSymbolicVariable renamingOfReturnStateVar) {
    	LLVMHeuristicState heuristicCallState = (LLVMHeuristicState) callState;
    	LLVMValue callStateVal = heuristicCallState.getValue((LLVMHeuristicVariable) renamingOfReturnStateVar);
    	
    	//TODO FEM: ask Jera about bounded/"normal" abstract int for intersecting. Add equalities to ITS?
    	//TODO FEM: do something like this in non-heuristic intersector, too?
    		
    }
    
    private static LLVMSymbolicVariable transitiveClosureOfMap(Map<LLVMSymbolicVariable,LLVMSymbolicVariable> map, LLVMSymbolicVariable key) {
    	LLVMSymbolicVariable mapping = map.get(key);
    	while(mapping != null && map.get(mapping)  != null) {
    		if(mapping.equals(map.get(mapping))) {
    			if(Globals.useAssertions) {
    				assert mapping instanceof LLVMHeuristicConstRef;
    			}
    			throw new IllegalStateException();
    		}
    		mapping = map.get(mapping);
    	}
    	return mapping;
    }
	
//    protected void cleanIntegerKnowledge() {
//    	LLVMHeuristicState intersection = ((LLVMHeuristicState) intersectedState);
//		for (IntegerRelation rel : intersection.getIntegerState().toRelationSet()) {
//			for(LLVMSymbolicVariable var : getAllLLVMSymbolicVariable(rel)) {
//				
//				LLVMHeuristicVariable hVar = (LLVMHeuristicVariable) var;
//				initValueInIntersectionIfNotPresent(hVar);
//			}
//		}
//	}
//    
//    private void initValueInIntersectionIfNotPresent(LLVMHeuristicVariable variable) {
//    	LLVMHeuristicState intersection = ((LLVMHeuristicState) intersectedState);
//    	LLVMValue val = intersection.getValue(variable);
//		if (val == null) {
//			intersectedState = intersection.setValue(variable,
//					AbstractInt.getUnknown(IntegerType.UNBOUND));
//		}
//    	
//    }
    
    //@Override
    //protected void addRelationsToIntersection(Set<LLVMRelation> relationsToAdd, Abortion aborter)
    //		throws IntersectionFailException {
    	/* In heuristic states, the following may happen: Adding a relation to a state may yield to the replacement of a certain symbolic variable by a constant.
    	 * This may result in the original symbolic variable to be removed from the state.
    	 * If we then add further relations that use a variable that was removed in such an earlier step, we get a problem.
    	 * 
    	 * We solve this problem by the following Eiertanz:
    	 * We perceive the relations to be added as a queue. If we try to add a relation referring to an unknown variable, we try to solve this problem by promoting it by one step in the queue.
    	 * We fallback to the original state before adding any of the relations and try adding them again, this time in the modified order.
    	 * 
    	 */
    	
    	/*List<LLVMRelation> relations = new ArrayList<>(relationsToAdd);
    	
    	LLVMHeuristicState originalIntersection = (LLVMHeuristicState) intersectedState;
    	LLVMHeuristicState currentIntersection = originalIntersection;
    	
    	boolean addedAll = false;
    	outerLoop:
    	while(!addedAll) {
    		currentIntersection = originalIntersection;
    		
    		for(int relIndex = 0; relIndex < relations.size(); relIndex++) {
    			LLVMRelation relationToAdd = relations.get(relIndex);
    			
    			Set<? extends LLVMSymbolicVariable> variablesInCurrentRelation =  relationToAdd.getVariables();
    			for(LLVMSymbolicVariable relationVariable : variablesInCurrentRelation) {
    				LLVMHeuristicVariable heuristicRelationVariable = (LLVMHeuristicVariable) relationVariable;
    				//Check if the current variable is known in the heuristic state:
    				if(currentIntersection.getValue(heuristicRelationVariable) == null) {
    					if(relIndex == 0) {
    						//Even the queuing trick didn't save us
    						throw new IllegalStateException("Was supposed to add relation which refers to unknown variable!");
    					}
    					LLVMRelation previousRel = relations.get(relIndex-1);
    					relations.set(relIndex, previousRel);
    					relations.set(relIndex-1, relationToAdd);
    					
    					continue outerLoop;
    				}
    			}
				
				
				if(currentIntersection.checkRelation(relationToAdd.negate(), aborter).x) {
	    			throw new IntersectionFailException("Inconsistent Knowledge");
	    		}
				
				currentIntersection = currentIntersection.addRelation(relationToAdd, aborter);
    		}
    		addedAll = true;
    	}
    	intersectedState = currentIntersection;
    	
    }*/
    
    //retFreshVar can also be a call state variable
    private LLVMSymbolicVariable resolveRetVarReplacement(LLVMSymbolicVariable retFreshVar) {
    	LLVMSymbolicVariable resultFromMap = transitiveClosureOfMap(replacements,retFreshVar);
    	return resultFromMap == null ? retFreshVar : resultFromMap;
    }
	
    @Override
	public Set<LLVMSymbolicVariable> getIntersectionNamesForVariable(LLVMSymbolicVariable callStateVariable) {
		Set<LLVMSymbolicVariable> intersectionVars = getCallStateVarToReturnStateVarsMap().get(callStateVariable)
				.stream()
				.map(retVar -> getReturnStateVarToFreshMap().get(retVar))
				.collect(Collectors.toCollection(LinkedHashSet::new));
		if(intersectedState.getSymbolicVariables().contains(callStateVariable)) {
			intersectionVars.add(callStateVariable);
		}
		
		Set<LLVMSymbolicVariable> result = new LinkedHashSet<>();
		for(LLVMSymbolicVariable retFreshVar : intersectionVars) {
			LLVMSymbolicVariable replacement = resolveRetVarReplacement(retFreshVar);
			
			if(replacement == null) {
				throw new IllegalStateException();
			}
			
			if(intersectedState.getSymbolicVariables().contains(replacement)) {
				result.add(replacement);
			}
		}
		
		/*if(!result.isEmpty() && !result.contains(callStateVariable)
				&& !result.stream().anyMatch(var -> var instanceof LLVMHeuristicConstRef)) {
			throw new IllegalStateException();
		}*/
		
		
		return result;
		
		
	}
    
    @Override
	/*public LLVMAllocation getNotDeallocatedIntersectedStateAllocation(LLVMAllocation callStateAllocation) {
		if(Globals.useAssertions) {
			assert getCallNode().getObject().getAllocations().contains(callStateAllocation);
		}
		
		
		//may be null
		LLVMAllocation returnStateAllocation = deallocationEvaluator.allocationBecameReturnStateAllocationWithoutDeallocationOnAllPaths(callStateAllocation);
		if(returnStateAllocation == null) {
			if(deallocationEvaluator.allocationLostDuringMergeWithoutDeallocationOnAllPaths(callStateAllocation)) {
				return handleAllocationRenaming(callStateAllocation);
			} else {
				return null;
			}
		} else {
			return handleAllocationRenaming(returnStateAllocation);
			
		}
	}*/

    protected LLVMAllocation handleAllocationRenaming(LLVMAllocation allocation, boolean fromCallState) {
    	Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> allocVars = LLVMAllocationDeallocationEvaluator.getVariablesFromAllocation(allocation);
		
		LLVMSimpleTerm lowerBoundRenaming = null;
		if(allocVars.x == null) {
			lowerBoundRenaming = allocation.x; //must have been a constant
		} else {
			if(fromCallState) {
				lowerBoundRenaming = resolveRetVarReplacement(allocVars.x);
			} else {
				lowerBoundRenaming = resolveRetVarReplacement(getReturnStateVarToFreshMap().get(allocVars.x));;
			}
		}
		
		LLVMSimpleTerm upperBoundRenaming = null;
		if(allocVars.y == null) {
			upperBoundRenaming = allocation.y; //must have been a constant
		} else {
			if(fromCallState) {
				upperBoundRenaming = resolveRetVarReplacement(allocVars.y);
			} else {
				upperBoundRenaming = resolveRetVarReplacement(getReturnStateVarToFreshMap().get(allocVars.y));
			}
		}

		
		LLVMAllocation retStateAllocationWithIntersectionNames = new LLVMAllocation(lowerBoundRenaming, upperBoundRenaming);
		if(!intersectedState.getAllocations().contains(retStateAllocationWithIntersectionNames)) {
			throw new IllegalStateException();
		}
		return retStateAllocationWithIntersectionNames;
    }
    

    
    
	//do not call unless intersection process is finished
	public LLVMMemoryRange getUnchangedIntersectedStateMemoryRange(LLVMMemoryRange callStateMemoryRange) {
		LLVMMemoryRange returnStateRange = unchangedEvaluator.turnedIntoReturnStateRangeOnAllPaths(callStateMemoryRange);
		
		if(returnStateRange == null) {
			return null;
		} else {
			Pair<LLVMSymbolicVariable,LLVMSymbolicVariable> rangeVars = LLVMUnchangedMemoryRelationEvaluator.getVariablesFromRange(returnStateRange);
			
			LLVMSimpleTerm lowerBoundRenaming = rangeVars.x == null ? callStateMemoryRange.getFromRef() :
				resolveRetVarReplacement(getReturnStateVarToFreshMap().get(rangeVars.x));
			
			LLVMSimpleTerm upperBoundRenaming = rangeVars.y == null ? callStateMemoryRange.getToRef() :
				resolveRetVarReplacement(getReturnStateVarToFreshMap().get(rangeVars.y));
			
			LLVMMemoryRange renamedIntersectionRange = new LLVMMemoryRange(lowerBoundRenaming, upperBoundRenaming, callStateMemoryRange.getType(), callStateMemoryRange.getUnsigned());
			
			if(!intersectedState.getMemory().containsKey(renamedIntersectionRange)) {
				throw new IllegalStateException();
			}
			
			return renamedIntersectionRange;
		}
	}
	
	protected void performPostProcessing() {
		//TODO FEM check if we should always do this
		intersectedState = ((LLVMHeuristicState) intersectedState).restrictToUsedReferences(null, aborter);
		super.performPostProcessing();
	}


}
