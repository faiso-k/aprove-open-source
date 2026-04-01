package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class Helpers {

	//Return those cycles in the FG which this node is on (and the index of the node on the cycle, as it may not be the first node)
	public static Set<Pair<LLVMSEPath,Integer>> getCycles(LLVMFunctionGraph fg, Node<LLVMAbstractState> node) {
		return fg.getCyclesAndPositionsOnThemForNode(node);
	}
	
	
	//gets only those cycles whose next node is not just the next node on the given path
	public static Set<Pair<LLVMSEPath,Integer>> getCyclesLeadingOutOfPath(LLVMFunctionGraph fg, Node<LLVMAbstractState> node, LLVMSEPath path, int nodeindex) {
		if(path.isCyclic() && nodeindex == path.size()-1) {
			throw new IllegalArgumentException("Do not ask for last state if path is cyclic, ask for first one");
		}
		
		Node<LLVMAbstractState> nextNodeInPath = getNextNodeInPossiblyCyclicPath(path,nodeindex);
		
		Set<Pair<LLVMSEPath,Integer>> allCycles = fg.getCyclesAndPositionsOnThemForNode(node);
		
		
		//return all those cycles whose next node is not the same node as the next node in the current path
		return allCycles
			.stream()
			.filter(cycleIndexPair -> getNextNodeInCyclicPath(cycleIndexPair.x,cycleIndexPair.y) != nextNodeInPath)
			.collect(Collectors.toCollection(LinkedHashSet::new));
		
	}
	
	
	//will never return null
	private static Node<LLVMAbstractState> getNextNodeInCyclicPath(LLVMSEPath cycle, int currentIndex) {
		if(Globals.useAssertions) {
			assert cycle.isCyclic();
		}
		
		if(currentIndex == cycle.size() - 1) {
			return cycle.get(1); //jump over 0, which is identical to currentnode
		} else {
			return cycle.get(currentIndex+1);
		}
		
	}
	
	//may return null if path is not cyclic and we are at the end of it
	static Node<LLVMAbstractState> getNextNodeInPossiblyCyclicPath(LLVMSEPath path, int currentIndex) {
		if(path.isCyclic()) {
			return getNextNodeInCyclicPath(path,currentIndex);
		} else {
			if(currentIndex == path.size() - 1) {
				return null;
			} else {
				return path.get(currentIndex+1);
			}
		}
		
	}
	
	
	public static boolean hasMultipleOutgoingEdges(LLVMFunctionGraph fg, LLVMSEPath path, int indexOnPath) {
		Node<LLVMAbstractState> node = path.get(indexOnPath);
		
		
		//TODO FEM: maybe pass the simple graph directly to the function?
		SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph = fg.getGraph();
		
		return graph.getOut(node).size() > 1;
		
	}
	
	public static Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> extractCallAndReturnNodeFromExecutionPaths(
			Set<LLVMSEPath> executionPaths) {
		LLVMSEPath someExecutionPath = executionPaths.iterator().next();
		
		return new Pair<>(someExecutionPath.get(0),someExecutionPath.get(someExecutionPath.size()-1));
	}
}
