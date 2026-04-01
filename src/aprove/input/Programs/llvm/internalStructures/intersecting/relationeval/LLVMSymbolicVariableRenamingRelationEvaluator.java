package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Created by Frank on 01.06.2017.
 */
public abstract class LLVMSymbolicVariableRenamingRelationEvaluator {
	
	protected final LLVMModule module;
	protected final LLVMImmutableFunctionGraph fg;
	
	
	protected final Node<LLVMAbstractState> callNode;
	protected final Node<LLVMAbstractState> returnNode;
	

    public LLVMSymbolicVariableRenamingRelationEvaluator(
    		LLVMImmutableFunctionGraph fg,
    		Node<LLVMAbstractState> callNode,
    		Node<LLVMAbstractState> returnNode,
    		LLVMModule module) {
		this.module = module;
		this.fg = fg;
		this.callNode = callNode;
		this.returnNode = returnNode;
	}

	public abstract Set<LLVMSymbolicVariable> getReturnStateVariablesForCallStateVariable(LLVMSymbolicVariable callStateVar);

	protected SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> getGraph() {
		return fg.getGraph();
	}
	
	protected LLVMFunctionGraph getFunctionGraph() {
		return fg;
	}
	
	protected LLVMModule getModule() {
		return module;
	}
    
	public abstract boolean isVariableConsistetOnCycles(Node<LLVMAbstractState> node, LLVMSymbolicVariable var);
	

	
	//we should be able to cache this (even globally?)
	//does not respect consistency of variable names along cycles, i.e., only local renaming
	//TODO FEM: should we use this on method skip edges?
	protected static Set<LLVMSymbolicVariable> getRenamingsOfSingleVariableOnSingleEdge(
			Node<LLVMAbstractState> currentNode,
			Node<LLVMAbstractState> nextNode,
			LLVMFunctionGraph fg,
			LLVMModule module,
			LLVMSymbolicVariable var ) {		
		SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph = fg.getGraph();
		LLVMEdgeInformation edgeToNextNode = graph.getEdgeObject(currentNode, nextNode);
		if(edgeToNextNode instanceof LLVMInstantiationInformation) {
			LLVMInstantiationInformation instantiationEdge = (LLVMInstantiationInformation) edgeToNextNode;
			Map<LLVMSimpleTerm, LLVMSimpleTerm> referenceCorrespondenceMap = instantiationEdge
					.getReferenceCorrespondenceMap();

			Set<LLVMSymbolicVariable> variablesInTarget = new LinkedHashSet<>();
			for (Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : referenceCorrespondenceMap.entrySet()) {
				LLVMSimpleTerm currentKey = entry.getKey();
				if (entry.getValue().equals(var)) {
					if(currentKey instanceof LLVMSymbolicVariable) {
					variablesInTarget.add( (LLVMSymbolicVariable) currentKey);
					} else {
						throw new IllegalStateException("Strange type");
					}
				}
			}
			return variablesInTarget;
		} else if(edgeToNextNode instanceof LLVMRefinementInformation 
				|| edgeToNextNode instanceof LLVMEvaluationInformation || edgeToNextNode instanceof LLVMCallAbstractionEdge) {
			return handleCallAbstractionEvaluationAndRefinement(
					currentNode,
					nextNode.getObject(),
					fg,
					module,
					var,
					edgeToNextNode instanceof LLVMEvaluationInformation);
		} else if(edgeToNextNode instanceof LLVMMethodSkipEdge) {
			LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edgeToNextNode;
			LLVMIntersectionResult iRes = skipEdge.getIntersectionResult();
			return iRes.getIntersectionNamesForVariable(var);
		} else {
			throw new IllegalStateException("Unsupported Edge Type");
		}
	}

	protected static Set<LLVMSymbolicVariable> handleCallAbstractionEvaluationAndRefinement(
			Node<LLVMAbstractState> currentNode,
			LLVMAbstractState nextState,
			LLVMFunctionGraph fg,
			LLVMModule module,
			LLVMSymbolicVariable var,
			boolean isEvaluation) {
		Set<LLVMSymbolicVariable> variablesInNextState = nextState.getSymbolicVariables();
		Set<LLVMSymbolicVariable> result = new LinkedHashSet<>();
		if (variablesInNextState.contains(var)) {
			result.add(var);
		}
		LLVMAbstractState currentState =  currentNode.getObject();
		
		//stays null if no variable reassigned
		Set<String> assignedVariable = Collections.emptySet();
		//stays empty if no store evaluated
		Set<LLVMMemoryRange> changedMemoryRanges = Collections.emptySet();
		boolean canUseProgVars = true;
		
		
		if(isEvaluation) {
			//LLVMEvaluationInformation evalInfo = (LLVMEvaluationInformation) edgeToNextNode;
			LLVMInstruction curInstr = currentState.getCurrentInstruction();
			
			if(curInstr instanceof LLVMStoreInstruction) {
				changedMemoryRanges = fg.getMemoryChangeTracker().getMemoryRangesInvalidatedByStore(currentNode);
			} else if(curInstr instanceof LLVMAssignmentInstruction) {
				LLVMAssignmentInstruction assignmentInstr = (LLVMAssignmentInstruction) currentState.getCurrentInstruction();
				assignedVariable = Collections.singleton(assignmentInstr.getProducedVariable());
			} else if(curInstr instanceof LLVMBranchInstruction ) {
				//if we evaluate branches, we "jump" over the phi instructions of the next block
				//without corresponding states in the graph!
				
				//collect variables assigned by phi nodes:
				
				String branchedTo = nextState.getCurrentBlock();					
			
				int instructionIndex = 0;
				LLVMProgramPosition pos = new LLVMProgramPosition(currentState.getCurrentFunction(), branchedTo, instructionIndex);
			        LLVMInstruction instruction = module.getInstruction(pos);
			        if (instruction instanceof LLVMPhiInstruction) {
			            final LLVMPhiInstruction phi = (LLVMPhiInstruction)instruction;
			            
			            if(assignedVariable.isEmpty()) {
			            	//avoid adding to Collections.emptySet
			            	assignedVariable = new LinkedHashSet<>();
			            }
			            assignedVariable.add(phi.getProducedVariable());
			            
			        }
			        pos = new LLVMProgramPosition(currentState.getCurrentFunction(), branchedTo, ++instructionIndex);
			} 
			
			if(curInstr instanceof LLVMCallInstruction || curInstr instanceof LLVMRetInstruction) {
				canUseProgVars = false;
			}
			
		}
		
		//If program variable x pointed to symbolic variable v in the current and w in the next state and x was not reassigned
		//then v in the current state corresponds to w in the next one
		//this does not hold when evaluating call and free, since we change stack frames then
		//TODO FEM: should we improve this so it can handle stack changes and lower stack frames?
		if(canUseProgVars) {
			for(Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> entry : currentState.getProgramVariables().entrySet() ) {
				if(entry.getValue().x.equals(var) && !assignedVariable.contains(entry.getKey())) {
					ImmutablePair<LLVMSymbolicVariable, LLVMType> progVarEntryNextState = nextState.getProgramVariables().get(entry.getKey());
					if(progVarEntryNextState != null && entry.getValue().y.equals(progVarEntryNextState.y) ) {
						//if(!result.contains(progVarEntryNextState.x)) {
						//	System.err.println("Added variable via prog vars");
						//}
						result.add(progVarEntryNextState.x);
					}
				}
			}
		}
		
		//If pointer v points to w in the current state and v points to u in the next state and pointer v was not invalidated by a store,
		//then w in the current state corresponds to u in the next one
		for(Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> eCur : currentState.getMemory().entrySet()) {
			LLVMMemoryRange curRange = eCur.getKey();
			
			if(changedMemoryRanges.contains(curRange)) {
				continue;
			}
			for(Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> eNext : nextState.getMemory().entrySet()) {
				LLVMMemoryRange nextRange = eNext.getKey();
				
				if(curRange.equals(nextRange)) {
					LLVMMemoryInvariant curInv = eCur.getValue();
					LLVMMemoryInvariant nextInv = eNext.getValue();
					
					if(curInv instanceof LLVMSimpleMemoryInvariant
							&& nextInv instanceof LLVMSimpleMemoryInvariant) {
						LLVMSimpleMemoryInvariant curSimple = (LLVMSimpleMemoryInvariant) curInv;
						LLVMSimpleMemoryInvariant nextSimple = (LLVMSimpleMemoryInvariant) nextInv;
						
						if(curSimple.getUsedReferences().size() == 1 && nextSimple.getUsedReferences().size() == 1 
								&& curSimple.getUsedReferences().contains(var)) {
							//if(!result.containsAll(nextInv.getUsedReferences())) {
							//	System.err.println("Added variable via heap entries");
							//}
							result.addAll(nextInv.getUsedReferences());
						}
					}

					
				}
			}
			
		}
		return result;
	}
	
	 

}
