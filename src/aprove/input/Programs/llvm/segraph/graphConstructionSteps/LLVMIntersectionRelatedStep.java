package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;


import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

public abstract class LLVMIntersectionRelatedStep extends LLVMAbstractGraphConstructionStep {

	

	public LLVMIntersectionRelatedStep(LLVMSEGraph graph) {
		super(graph);
	}

	protected LLVMFunctionGraph getFunctionGraphForFunction(String functionName) {
		if(Globals.useAssertions) {
			assert getIntersectionHeuristics().isIntersectableFunction(functionName);
		}
		return graph.getFunctionGraphTracker().getFunctionGraph(functionName);
	}

	/*protected LLVMFunctionGraph getFunctionGraph() {
		throw new NotImplementedException();
	}*/
	
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<Node<LLVMAbstractState>> getNeededReturnNodesOfFunction(LLVMSEGraph graph, String functionName) {
		if(Globals.useAssertions) {
			assert !functionName.startsWith("@");
		}
		
		Predicate<? super Node<LLVMAbstractState>> isReturnStateOfGivenFunction = 
				node -> (isReturnState(graph, node.getObject()) && node.getObject().getCurrentFunction().equals(functionName)) && !graph.isNodeUnneeded(node);
				
		return graph.getNodes().stream()
				.filter(isReturnStateOfGivenFunction)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	@Deprecated
	public static boolean hasNeededGeneralization(LLVMSEGraph graph, Node<LLVMAbstractState> node) {
			return graph.getOutEdges(node).
					stream().
					anyMatch(edge -> (edge.getObject() instanceof LLVMInstantiationInformation && !graph.isNodeUnneeded(edge.getEndNode())));
					
	}
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<Node<LLVMAbstractState>> getNeededReturnNodesNeedingIntersectionsOfFunction(LLVMSEGraph graph, String functionName) {
		if(Globals.useAssertions) {
			assert !functionName.startsWith("@");
		}
		Predicate<? super Node<LLVMAbstractState>> hasNoGeneralization = 
				node -> (graph.getOutEdges(node).stream().
					noneMatch(edge -> (edge.getObject() instanceof LLVMInstantiationInformation)));
		
		Predicate<? super Node<LLVMAbstractState>> hasNoIncomingFunctionSkipFailureEdge = 
				node -> (graph.getInEdges(node).stream().
					noneMatch(edge -> (edge.getObject() instanceof LLVMFunctionSkipFailureEdge)));
				
		return getNeededReturnNodesOfFunction(graph, functionName).stream()
				.filter(hasNoGeneralization)
				.filter(hasNoIncomingFunctionSkipFailureEdge)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<Node<LLVMAbstractState>> getNeededCallNodesOfFunction(LLVMSEGraph graph, String functionName) {
		if(Globals.useAssertions) {
			assert !functionName.startsWith("@");
		}
		
		Predicate<? super Node<LLVMAbstractState>> isCallStateOfGivenFunction = 
				node -> (isCallState(graph, node.getObject()) && node.getObject().getCurrentFunction().equals(functionName)) && !graph.isNodeUnneeded(node);
		
		return graph.getNodes().stream()
				.filter(isCallStateOfGivenFunction)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<Node<LLVMAbstractState>> getNeededCallNodesNeedingIntersectionsOfFunction(LLVMSEGraph graph, String functionName) {
		if(Globals.useAssertions) {
			assert !functionName.startsWith("@");
		}
		
		Predicate<? super Node<LLVMAbstractState>> hasNoGeneralization = 
				node -> (graph.getOutEdges(node).stream().
					noneMatch(edge -> (edge.getObject() instanceof LLVMInstantiationInformation)));
		
		return getNeededCallNodesOfFunction(graph,functionName).stream()
				.filter(hasNoGeneralization)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	/*public static Set<Node<LLVMAbstractState>> getNeededCallAbstractionNodesOfFunction(LLVMSEGraph graph, String functionName) {
		if(Globals.useAssertions) {
			assert !functionName.startsWith("@");
		}
		
		Set<Node<LLVMAbstractState>> callNodes = getNeededCallNodesOfFunction(graph, functionName);
		Set<Node<LLVMAbstractState>> callAbstractions = new LinkedHashSet<>();
		
		for(Node<LLVMAbstractState> callNode : callNodes) {
			int foundNeeded = 0;
			for(Edge<LLVMEdgeInformation,LLVMAbstractState> edge : graph.getOutEdges(callNode)) {
				if(edge.getObject() instanceof LLVMCallAbstractionEdge && !graph.isNodeUnneeded(edge.getEndNode())) {
					callAbstractions.add(edge.getEndNode());
					foundNeeded++;
				}
			}
			if(Globals.useAssertions) {
				assert foundNeeded <= 1;
			}
		}
		
		return callAbstractions;
	}*/
	
	//public static Set<Node<LLVMAbstractState>> getNeededIntersections(LLVMSEGraph graph, String functionName)
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<LLVMIntermediateIntersectionResult> getNeededIntersections(LLVMSEGraph graph) {
		Set<LLVMIntermediateIntersectionResult> intersections = new LinkedHashSet<>();

		for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getEdges()) {
			if (edge.getObject() instanceof LLVMMethodSkipEdge) {
				LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
				if (!graph.isNodeUnneeded(edge.getEndNode())) {
					intersections.add(skipEdge.getIntersectionResultOld());
				}
			}
		}

		return intersections;
	}
	
	@Deprecated
	public static Set<LLVMSEPath> getAllPathsFromCallToReturnViaCallAbstraction(LLVMSEGraph graph, Node<LLVMAbstractState> callNode,
			Node<LLVMAbstractState> returnNode) {
		
		LLVMSEPath pathFromCallToEntry = getPathFromCallNodeToEntryNode(graph, callNode);
		
		if(pathFromCallToEntry == null) {
			return Collections.emptySet();
		}
		
		Node<LLVMAbstractState> entryNode = pathFromCallToEntry.getLast();
		
		List<LLVMSEPath> allPathsFromEntryToReturn = LLVMSEPath.backtrackPath(graph, entryNode, returnNode, Collections.singleton(LLVMIntersectionInstantiationInformation.class));
		
		Set<LLVMSEPath> combinedPaths = new LinkedHashSet<>();
		
		for(LLVMSEPath currentPath : allPathsFromEntryToReturn) {
			combinedPaths.add(LLVMSEPath.mergePathsWithOverlappingEndAndStart(pathFromCallToEntry, currentPath));
		}
		return combinedPaths;
	}
	
	@Deprecated
	public static Node<LLVMAbstractState> getCallAbstractionOfCallNode(LLVMSEGraph seGraph, Node<LLVMAbstractState> callNode) {
		Set<Node<LLVMAbstractState>> foundCallAbstractions = new LinkedHashSet<>();
		
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> outEdge : seGraph.getOutEdges(callNode)) {
			if(outEdge.getObject() instanceof LLVMCallAbstractionEdge) {
				foundCallAbstractions.add(outEdge.getEndNode());
			}
		}
		
		if(foundCallAbstractions.isEmpty()) {
			return null;
		} else {
			if(Globals.useAssertions) {
				assert foundCallAbstractions.size() == 1: "GRAPH CONSISTENCY ERROR: There are several call abstractions";
			}
			return foundCallAbstractions.iterator().next();
		}
	}
	
	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static LLVMIntermediateIntersectionResult getNeededIntersectionOfGivenCallAndReturnNodeRespectingLargestSubsetOfPaths(LLVMSEGraph graph, Set<LLVMSEPath> paths, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		Set<LLVMIntermediateIntersectionResult> intersections = LLVMIntersectionRelatedStep.getNeededIntersections(graph);
		
		LLVMIntermediateIntersectionResult foundIntersection = null;
		
		for (LLVMIntermediateIntersectionResult intersection : intersections) {
			if (intersection.getCallNode() == callNode && intersection.getReturnNode() == returnNode) {
				if (foundIntersection != null && Globals.useAssertions) {
					assert !foundIntersection.getRespectedPathsFromCallToReturnState().equals(intersection.getRespectedPathsFromCallToReturnState()) :
						"Must not have more than one needed intersection for the same call&return node and same paths in the graph";
				}
				if(paths.containsAll(intersection.getRespectedPathsFromCallToReturnState())){
					//The current intersection respects a subset of the paths we're looking for
					
					
					if(foundIntersection == null || intersection.getRespectedPathsFromCallToReturnState().containsAll(foundIntersection.getRespectedPathsFromCallToReturnState())) {
						//The current intersection respects a superset of the paths of the previously found one
						foundIntersection = intersection;
					}
					
				}
				

			}
		}
		
		return foundIntersection;
	}
	

	@Deprecated//This should be done by [Entry|Return|Call|Intersted]StateTracker in the future
	public static Set<LLVMIntermediateIntersectionResult> getNeededIntersectionsWithGivenReturnState(LLVMSEGraph graph, Node<LLVMAbstractState> returnNode) {
		return getNeededIntersections(graph).stream().
				filter(intersection -> intersection.getReturnNode() == returnNode).
				collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	@Deprecated
	public static LLVMSEPath getPathFromCallNodeToEntryNode(LLVMSEGraph graph, Node<LLVMAbstractState> callNode) {
		ArrayList<Node<LLVMAbstractState>> path = new ArrayList<>();
		path.add(callNode);
		
		
		Node<LLVMAbstractState> callAbstractionNode = getCallAbstractionOfCallNode(graph, callNode);
		
		if(callAbstractionNode == null) {
			return null;
			//There ist no call abstraction (yet?)
		}
		
		
		
		Node<LLVMAbstractState> entryNode = callAbstractionNode;
		while(entryNode != null) {
			path.add(entryNode);
			entryNode = getGeneralization(graph, entryNode);
		}
		
		entryNode = path.get(path.size()-1);
		
		if(Globals.useAssertions) {
			assert isCallAbstractionOrEntryState(graph, path.get(path.size()-1).getObject());
			//assert graph.getCurrentEntryNodeForFunction(entryNode.getObject().getCurrentFunction()) == entryNode;
		}
		
		return new LLVMSEPath(path, graph);
	}
	
	@Deprecated
	public static boolean hasMatchingFunctionSkipFailureEdgeInGraph(LLVMSEGraph graph, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, Set<LLVMSEPath> respectedPaths ) {
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getEdges()) {
			if(edge.getObject() instanceof LLVMFunctionSkipFailureEdge) {
				LLVMFunctionSkipFailureEdge failureEdge = (LLVMFunctionSkipFailureEdge) edge.getObject();
				
				if(failureEdge.getCallNode().equals(callNode) && failureEdge.getReturnNode().equals(returnNode) && failureEdge.getRespectedPaths().equals(respectedPaths)) {
					return true;
				}
			}
		}
		return false;
	}
	
	//This throws an exception if there are multiple outgoing generalization edges! Ignores needed/unneeded
	@Deprecated
	private static Node<LLVMAbstractState> getGeneralization(LLVMSEGraph graph, Node<LLVMAbstractState> node) {
		Edge<LLVMEdgeInformation, LLVMAbstractState> foundEdge = null;
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> currentEdge : graph.getOutEdges(node)) {
			if(currentEdge.getObject() instanceof LLVMInstantiationInformation) {
				if(Globals.useAssertions) {
					assert foundEdge == null : "GRAPH CONSISTENCY ERROR: More than one outgoing generalization edge of an entry state";
				}
				foundEdge = currentEdge;
			}
		}
		
		return foundEdge == null ? null : foundEdge.getEndNode();
	}
	
	

}
