package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMRecursiveSymbolicVariableRenamingRelationEvaluator extends LLVMSymbolicVariableRenamingRelationEvaluator{

	private Map<Node<LLVMAbstractState>,Map<LLVMSymbolicVariable,Boolean>> consistent;
	private Set<LLVMSEPath> executionPaths;
	
	
	public LLVMRecursiveSymbolicVariableRenamingRelationEvaluator(LLVMImmutableFunctionGraph fg,
			Set<LLVMSEPath> executionPaths, LLVMModule module) {	
		super(fg,
				Helpers.extractCallAndReturnNodeFromExecutionPaths(executionPaths).x,
				Helpers.extractCallAndReturnNodeFromExecutionPaths(executionPaths).y,
				module);
		consistent = new LinkedHashMap<>();
		this.executionPaths = executionPaths;
	}


	static class StackEntry {
		
		
		
		public StackEntry(LLVMSEPath path, int nodeIndexOnPath, LLVMSymbolicVariable var) {
			super();
			this.path = path;
			this.nodeIndexOnPath = nodeIndexOnPath;
			this.var = var;
		}
		
		//TODO FEM: use == based equals on other occasions for LLMSEPath, too?
		
		
		
		LLVMSEPath path;
		int nodeIndexOnPath;
		LLVMSymbolicVariable var;
		@Override
		
		//respects path based on identity
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + nodeIndexOnPath;
			result = prime * result + ((path == null) ? 0 : System.identityHashCode(path));
			result = prime * result + ((var == null) ? 0 : var.hashCode());
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
			if (var == null) {
				if (other.var != null)
					return false;
			} else if (!var.equals(other.var))
				return false;
			return true;
		}
	}
	
	
	

	@Override
	public Set<LLVMSymbolicVariable> getReturnStateVariablesForCallStateVariable(LLVMSymbolicVariable callStateVar) {
		Set<LLVMSymbolicVariable> result = null;
		for(LLVMSEPath executionPath : executionPaths) {
			
			Set<LLVMSymbolicVariable> resultForPath = getRenamingRecursive(executionPath,0,callStateVar, new LinkedHashSet<>(),getModule(),getFunctionGraph(), true);
			
			if(result == null) {
				result = resultForPath;
			} else {
				result.retainAll(resultForPath);
			}
			
			if(result.isEmpty())
				break;
			
		}
		
		return result;
	}
	
	@Override
	protected SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> getGraph() {
		return fg.getGraph();
	}
	
	protected LLVMFunctionGraph getFunctionGraph() {
		return fg;
	}
	
	//stack must be allowed to be changed
	public static Set<LLVMSymbolicVariable> getRenamingRecursive(LLVMSEPath path, int nodeIndexOnPath, LLVMSymbolicVariable variable, LinkedHashSet<StackEntry> stack, LLVMModule module, LLVMFunctionGraph functionGraph, boolean respectCycles) {
		StackEntry entryForThisInvocation = new StackEntry(path, nodeIndexOnPath, variable);
		boolean isCyclic = path.isCyclic();
		
		
		Node<LLVMAbstractState> curNode = path.get(nodeIndexOnPath);
		if(stack.contains(entryForThisInvocation)) {
			//We do not want to descend into the same cycle again
			if(isCyclic) {
				//"everything ok" signal.
				return Collections.singleton(variable);
			} else {
				throw new IllegalStateException("saw non-cyclic path twice. what to do?");
			}
			
		}
		stack.add(entryForThisInvocation);

		
		Set<LLVMSymbolicVariable> currentRenaming = new LinkedHashSet<>();
		currentRenaming.add(variable);
		
		
		
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

			if(respectCycles && Helpers.hasMultipleOutgoingEdges(functionGraph, path, curIndex)) {
				Iterator<LLVMSymbolicVariable> curVarIterator = currentRenaming.iterator();
				
				while (curVarIterator.hasNext()) {
					LLVMSymbolicVariable curVar = curVarIterator.next();
					Set<Pair<LLVMSEPath, Integer>> cyclePairs = Helpers.getCyclesLeadingOutOfPath(functionGraph, curNode,path,curIndex);
					for (Pair<LLVMSEPath, Integer> p : cyclePairs) {
						Set<LLVMSymbolicVariable> renaming = getRenamingRecursive(p.x,p.y,curVar,new LinkedHashSet<>(stack),module,functionGraph, respectCycles);
						if(!renaming.contains(curVar)) {
							curVarIterator.remove();
							break; //continue outer loop
						}
						
					}
				}
				
			}
			
			if(currentRenaming.isEmpty()) {
				return Collections.emptySet();
			}
			
			Set<LLVMSymbolicVariable> nextNodeVars = new LinkedHashSet<>();
			for(LLVMSymbolicVariable curVar : currentRenaming) {
				Set<LLVMSymbolicVariable> namesInNextNode = getRenamingsOfSingleVariableOnSingleEdge(curNode, nextNode, functionGraph, module, curVar);
				nextNodeVars.addAll(namesInNextNode);
			}
			
			currentRenaming = nextNodeVars;
			//end logic
			
			curNode = nextNode;
			curIndex = nextIndex;
			
			
		}
		return currentRenaming;
	}
	
	
	//TODO FEM: right now this is not used in getRenamingRecursive. should we change that?
	public boolean isVariableConsistetOnCycles(Node<LLVMAbstractState> node, LLVMSymbolicVariable var) {
		Map<LLVMSymbolicVariable,Boolean> consistencyMapForNode = consistent.computeIfAbsent(node, n -> new LinkedHashMap<>());
		
		Boolean mapResult = consistencyMapForNode.get(var);
		
		if(mapResult == null) {
			Set<Pair<LLVMSEPath,Integer>> cyclesAndPositions = Helpers.getCycles(getFunctionGraph(), node);
			
			for(Pair<LLVMSEPath,Integer> pair : cyclesAndPositions) {
				LLVMSEPath curCycle = pair.x;
				int positionInCycle = pair.y;
				Set<LLVMSymbolicVariable> renamingAlongCycle = getRenamingRecursive(curCycle,positionInCycle,var, new LinkedHashSet<>(), getModule(), getFunctionGraph(), true);
				if(!renamingAlongCycle.contains(var)) {
					//variable is not mapped to itself along cycle
					consistencyMapForNode.put(var, false);
					return false;
				}
				
			}
			//variable is mapped to itself along all cycles (also when recursively desecnding into subcycles)
			consistencyMapForNode.put(var, true);
			return true;
			
			
		}
		return mapResult;
	}
	
}
