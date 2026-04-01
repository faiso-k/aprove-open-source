package aprove.input.Programs.llvm.utils.static_analysis;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMCallGraph {
	
	public LLVMCallGraph(LLVMModule module) {
		this.module = module;
	}
	
	private SimpleGraph<String, Object> callGraph;
	private LLVMModule module;
	Map<String, Node<String>> functionNamesToNode;
	
	private void create() {
		callGraph = new SimpleGraph<>();
		
		
		Map<String,LLVMFnDeclaration> functionMap = module.getFunctions();
		
		Set<LLVMProgramPosition>  allProgramPositions = LLVMModule.getAllPositions(functionMap.values());
		
		functionNamesToNode = new LinkedHashMap<>();
		
		for(LLVMProgramPosition  currentPosition : allProgramPositions) {
			String currentFunction = currentPosition.x;
			
			Node<String> nodeForCurrentFunction = functionNamesToNode.get(currentFunction);
			
			if(nodeForCurrentFunction == null) {
				nodeForCurrentFunction = new Node<String>(currentFunction);
				functionNamesToNode.put(currentFunction, nodeForCurrentFunction);
				callGraph.addNode(nodeForCurrentFunction);
			}
			
			
			LLVMInstruction currentInstruction = module.getInstruction(currentPosition);
			
			if(currentInstruction instanceof LLVMCallInstruction) {
				LLVMCallInstruction callInstruction = (LLVMCallInstruction) currentInstruction;
				
				String calledFunction = callInstruction.getFunctionName().getNameWithoutScope();
				
				Node<String> nodeForCalledFunction = functionNamesToNode.get(calledFunction);
				
				if(nodeForCalledFunction == null) {
					nodeForCalledFunction = new Node<String>(calledFunction);
					functionNamesToNode.put(calledFunction, nodeForCalledFunction);
				}
				
				callGraph.addEdge(nodeForCurrentFunction, nodeForCalledFunction);
			}
			
			
		}

	}
	
	public Set<String> getRecursiveFunctions() {
		if(callGraph == null)
			create();
		
		return callGraph.getSCCs()
				.stream()
				.flatMap(s -> s.stream())
				.map(n -> n.getObject())
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public Set<String> functionsCalledBy(String function) {
		Node<String> callGraphNode = functionNamesToNode.get(function);
		
		if(callGraphNode == null)
			return Collections.emptySet();
		
		return callGraph.getOut(callGraphNode)
				.stream()
				.map(n -> n.getObject())
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public Set<String> functionsCalledByTransitive(String function) {
		Node<String> callGraphNode = functionNamesToNode.get(function);
		
		Set<Node<String>> reachableNodes = callGraph.determineReachableNodes(Collections.singleton(callGraphNode));
		
		return reachableNodes
				.stream()
				.map(n -> n.getObject())
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
}
