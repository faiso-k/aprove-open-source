package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

//updated
public class LLVMNewIntersectionNeededListener extends LLVMSEGraphEventListenerSkeleton{

	public LLVMNewIntersectionNeededListener(LLVMSEGraph graph) {
		super(graph);
	}
	
	private Set<LLVMFunctionGraph> getFunctionGraphs() {
		return graph.getFunctionGraphTracker().getAllFunctionGraphs();
	}
	

	@Override
	public List<LLVMAbstractGraphConstructionStep> completedGraphConstructionIterationEvent() {
		List<LLVMAbstractGraphConstructionStep> creationSteps = new ArrayList<>();
		for(LLVMFunctionGraph fg : getFunctionGraphs()) {
			creationSteps.addAll(getCreationStepsForNewIntersectionsOfFunction(fg));
		}
		return creationSteps;
		
	}



	private List<LLVMAbstractGraphConstructionStep> getCreationStepsForNewIntersectionsOfFunction(LLVMFunctionGraph fg) {
		List<LLVMAbstractGraphConstructionStep> creationSteps = new ArrayList<>();
		
		Set<Node<LLVMAbstractState>> callNodes = fg.getCallNodes();
		
		Set<Node<LLVMAbstractState>> returnNodesWithoutGeneralization = fg.getNonGeneralizedReturnNodes();
		
		for(Node<LLVMAbstractState> callNode : callNodes) {
			for(Node<LLVMAbstractState> returnNode : returnNodesWithoutGeneralization) {
				creationSteps.addAll(createNecessaryStepsForSpecificPairOfCallAndReturnNodes(fg, callNode,returnNode));
			}
		}
		
		return creationSteps;
	}


	

	private List<LLVMAbstractGraphConstructionStep> createNecessaryStepsForSpecificPairOfCallAndReturnNodes(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		if(needToCreateNewIntersection(fg,callNode,returnNode)) {
			return Collections.singletonList(new LLVMCreateIntersectionStep(graph,fg, callNode, returnNode));
		} else {
			return Collections.emptyList();
		}
		
		
		

	}
	
	//todo: should we check if the return node is generalized?
	public static boolean needToCreateNewIntersection(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		if(fg.isPathAgnostic()) {
			
			ArrayList<Node<LLVMAbstractState>> singleExecutionPath = fg.getSingleExecutionPathViaMostGeneralEntryState(callNode, returnNode);
			
			if(singleExecutionPath == null) {
				return false;
			}
			
			LLVMIntersectionResult existingIntersection = fg.getMostRecentIntersection(callNode, returnNode);
			return existingIntersection == null;
		} else {
			Set<LLVMSEPath> executionPaths = fg.getExecutionPathsViaMostGeneralEntryState(callNode, returnNode);
			
			Set<LLVMSEPath> relevantCycles = fg.getAllCyclesReachableFromExecutionPaths(executionPaths);
			
			if(executionPaths.isEmpty() || fg.hasMatchingFunctionSkipFailureEdgeInGraph(callNode,returnNode, executionPaths, relevantCycles)) {
				//There is no path (yet) or there is a failure for the given intersection, we don't have to do anything
				return false;
			}
			
			LLVMIntersectionResult existingIntersection = fg.getMostRecentIntersection(callNode, returnNode);
			if(existingIntersection != null) {
				Set<LLVMSEPath> respectedExecutionPaths = new LinkedHashSet<>(existingIntersection.getRespectedExecutionPaths());
				
				Set<LLVMSEPath> respectedCycles = new LinkedHashSet<>(existingIntersection.getRespectedCycles());
				
				if(respectedExecutionPaths.containsAll(executionPaths) && respectedCycles.containsAll(relevantCycles)) {
					//The intersection we found respects all paths 
					return false;
				} 
			}
		}
		return true;
	}

}
