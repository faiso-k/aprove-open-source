package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class LLVMStateBasedSymbolicVariableRenamingRelationEvaluator extends LLVMSymbolicVariableRenamingRelationEvaluator {

	public LLVMStateBasedSymbolicVariableRenamingRelationEvaluator(
			LLVMImmutableFunctionGraph fg,
			Node<LLVMAbstractState> callNode,
    		Node<LLVMAbstractState> returnNode,
    		LLVMModule module) {
		super(fg, callNode, returnNode, module);
		pathToMostGeneralEntryNode = new LLVMSEPath(fg.getPathToMostGeneralEntryNodeFromCallNode(callNode), fg.getGraph());
		entryNodeVarToCallNodeVarMap = new LinkedHashMap<>();
		cache = new LinkedHashMap<>();
		
		
		for(LLVMSymbolicVariable callNodeVar : callNode.getObject().getSymbolicVariables()) {
			Set<LLVMSymbolicVariable> entryStateVars = 
					LLVMRecursiveSymbolicVariableRenamingRelationEvaluator.getRenamingRecursive(pathToMostGeneralEntryNode, 0, callNodeVar, new LinkedHashSet<>(), module, fg, false);
			
			for(LLVMSymbolicVariable entryStateVar : entryStateVars) {
				Set<LLVMSymbolicVariable> mapEntry = entryNodeVarToCallNodeVarMap.computeIfAbsent(entryStateVar, x -> new LinkedHashSet<>());
				mapEntry.add(callNodeVar);
				
			}
		}
		
		
		
	}
	
	private final LLVMSEPath pathToMostGeneralEntryNode;
	private final Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> entryNodeVarToCallNodeVarMap;
	private final Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> cache;
	
	
	@Override
	public Set<LLVMSymbolicVariable> getReturnStateVariablesForCallStateVariable(LLVMSymbolicVariable callStateVar) {
		Set<LLVMSymbolicVariable> cacheResult = cache.get(callStateVar);
		if(cacheResult != null) {
			return cacheResult;
		} else {
			Set<LLVMSymbolicVariable> result = new LinkedHashSet<>();
			
			
			
			for(Map.Entry<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> e : returnNode.getObject().getEntryStateVarCorrespondenceMap().entrySet()) {
				LLVMSymbolicVariable entryStateVar = e.getKey();
				Set<LLVMSymbolicVariable> returnStateVars = e.getValue();
				
				Set<LLVMSymbolicVariable> callNodeVars = entryNodeVarToCallNodeVarMap.get(entryStateVar);
				
				if(callNodeVars != null && callNodeVars.contains(callStateVar)) {
					result.addAll(returnStateVars);
				}
			} 
			
			cache.put(callStateVar, result);
			return result;
		}
		
		
	}

	@Override
	public boolean isVariableConsistetOnCycles(Node<LLVMAbstractState> node, LLVMSymbolicVariable var) {
		throw new UnsupportedOperationException();
	}
	
	public static LLVMAbstractState handleVarToEntryStateMapForEvaluationOrRefinement(
			LLVMFunctionGraph fg,
			LLVMModule module,
			Node<LLVMAbstractState> baseNode,
			LLVMAbstractState successorState,
			boolean isEvaluation
			) {
		LLVMAbstractState baseState = baseNode.getObject();
		
		ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> baseStateMap = baseState.getEntryStateVarCorrespondenceMap();
		
		Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> succesorMap = new LinkedHashMap<>();
		
		for(Map.Entry<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> e : baseStateMap.entrySet() ) {
			LLVMSymbolicVariable entryStateVar = e.getKey();
			for(LLVMSymbolicVariable baseStateVar : e.getValue()) {
				Set<LLVMSymbolicVariable> successorVars = handleCallAbstractionEvaluationAndRefinement(baseNode,successorState,fg,module,baseStateVar,isEvaluation);
				
				Set<LLVMSymbolicVariable> succesorSetInMap = succesorMap.computeIfAbsent(entryStateVar, v -> new LinkedHashSet<>());
				succesorSetInMap.addAll(successorVars);
			}
			
		}
		
		
		Map<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> resultMapMutable = new LinkedHashMap<>();
		for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> e : succesorMap.entrySet()) {
			if(!e.getValue().isEmpty()) {
				//we don't want empty sets in the map, just omit the whole entry
				resultMapMutable.put(e.getKey(), ImmutableCreator.create(e.getValue()));
			}
		}
		
		return successorState.setVarToEntryStateVarsMap(ImmutableCreator.create(resultMapMutable));
		
	}
	
	public static LLVMAbstractState handleCallStateToIntersectionEntryStateVarMap(LLVMIntersector intersector, LLVMAbstractState intersectedState) {
		LLVMAbstractState callState = intersector.getCallNode().getObject();
		ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> callStateMap = callState.getEntryStateVarCorrespondenceMap();
		
		Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> intersectionMap = new LinkedHashMap<>();
		
		for(Map.Entry<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> e : callStateMap.entrySet() ) {
			LLVMSymbolicVariable entryStateVar = e.getKey();
			for(LLVMSymbolicVariable callStateVar : e.getValue()) {
				Set<LLVMSymbolicVariable> successorVars = intersector.getIntersectionNamesForVariable(callStateVar);
				
				Set<LLVMSymbolicVariable> succesorSetInMap = intersectionMap.computeIfAbsent(entryStateVar, v -> new LinkedHashSet<>());
				succesorSetInMap.addAll(successorVars);
			}
			
		}
		
		Map<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> resultMapMutable = new LinkedHashMap<>();
		for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> e : intersectionMap.entrySet()) {
			if(!e.getValue().isEmpty()) {
				//we don't want empty sets in the map, just omit the whole entry
				resultMapMutable.put(e.getKey(), ImmutableCreator.create(e.getValue()));
			}
		}
		
		return intersectedState.setVarToEntryStateVarsMap(ImmutableCreator.create(resultMapMutable));
		
	}
	
	public static LLVMAbstractState generalizationPostProcessing(LLVMAbstractState generalizedState, LLVMAbstractState postProcessedGeneralizedState) {
		ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> genStateMap = generalizedState.getEntryStateVarCorrespondenceMap();
		
		Set<LLVMSymbolicVariable> postProcessedStateVars = postProcessedGeneralizedState.getSymbolicVariables();
		
		Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> succesorMap = new LinkedHashMap<>();
		
		for(Map.Entry<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> e : genStateMap.entrySet() ) {
			LLVMSymbolicVariable entryStateVar = e.getKey();
			for(LLVMSymbolicVariable baseStateVar : e.getValue()) {
				if(postProcessedStateVars.contains(baseStateVar)) {
					Set<LLVMSymbolicVariable> succesorSetInMap = succesorMap.computeIfAbsent(entryStateVar, v -> new LinkedHashSet<>());
					succesorSetInMap.add(baseStateVar);
				}
			}
			
		}
		
		
		Map<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> resultMapMutable = new LinkedHashMap<>();
		for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> e : succesorMap.entrySet()) {
			if(!e.getValue().isEmpty()) {
				//we don't want empty sets in the map, just omit the whole entry
				resultMapMutable.put(e.getKey(), ImmutableCreator.create(e.getValue()));
			}
		}
		
		return postProcessedGeneralizedState.setVarToEntryStateVarsMap(ImmutableCreator.create(resultMapMutable));
	}
	
	public static LLVMAbstractState initEntryStateVarMapForEntryState(LLVMAbstractState entryState) {
		Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> map = new LinkedHashMap<>();
		for(LLVMSymbolicVariable var : entryState.getSymbolicVariables()) {
			if(var instanceof LLVMHeuristicConstRef) {
				//a constant will always stay a constant
				
				continue;
			}
			
			map.put(var, Collections.singleton(var));
		}
		
		Map<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> resultMapMutable = new LinkedHashMap<>();
		for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> e : map.entrySet()) {
			resultMapMutable.put(e.getKey(), ImmutableCreator.create(e.getValue()));
		}
		
		return entryState.setVarToEntryStateVarsMap(ImmutableCreator.create(resultMapMutable));
	}

}
