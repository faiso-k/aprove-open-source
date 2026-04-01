package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMSEGraphIntegrityChecker extends LLVMSEGraphEventListenerSkeleton {

	
	
	public LLVMSEGraphIntegrityChecker(LLVMSEGraph graph) {
		super(graph);
	}


	@Override
	public void graphFinishedEvent() {
		System.err.println("Graph finished, checking  consistency");
		long startTime = System.currentTimeMillis();
		if (Globals.useAssertions) {
			checkNumberOfSucessors();
			havePredecessors();
			outgoingEdgesAreConsistent();
			allNeededNodesHavePathToNeededEndNode();
			haveAtLeastOneEndState();
			
			atMostOneReturnStateWithoutGeneralizationPerPairOfProgramPositionAndProgramVariables();
			if(!graph.getFunctionGraphTracker().getAllFunctionGraphs().isEmpty()) {
				eachCallStateReachesAtLeastOneReturnState();
				allIntersectionsExist();
			}
			
		}
		System.err.println("Graph finished, checked consistency, took " + (System.currentTimeMillis() - startTime) / 1000.0 + "s" );

	}
	
	protected void checkNumberOfSucessors() {
		for(Node<LLVMAbstractState> node : graph.getNodes()) {
			if(graph.isNodeUnneeded(node))
				continue;
			
			if(getIntersectionHeuristics().isReturnState(node.getObject())) {
				assert allSucessorsAreGeneralzations(node);
			} else if(getIntersectionHeuristics().isCallState(node.getObject())) {
				assert getNumberOfOutgoingEdges(node) >= 1;
			} else if(getNumberOfOutgoingEdges(node) >= 2) {
                assert allSucessorsAreRefinements(node);
            } else if(node.getObject().isErrorState()) {
                assert allSucessorsAreGeneralzations(node);
            } else if(node.getObject().isInconsistentState()) {
                assert allSucessorsAreGeneralzations(node);
            } else {
            	if(LLVMDebuggingFlags.PERFORM_GRAPH_CONSISTENCY_CHECKS_FOR_TERMINATING_FUNCTIONS) {
            		assert getNumberOfOutgoingEdges(node) == 1;
            	}
			}
		}
	}
	
	
	private int getNumberOfOutgoingEdges(Node<LLVMAbstractState> node) {
		return graph.getOut(node).size();
	}
	
	protected void allNeededNodesHavePathToNeededEndNode() {
		if(LLVMDebuggingFlags.PERFORM_GRAPH_CONSISTENCY_CHECKS_FOR_TERMINATING_FUNCTIONS) {
			Set<Node<LLVMAbstractState>> neededEndNodes = getEndAndErrorNodes();
	
			outer: for (Node<LLVMAbstractState> node : graph.getNodes()) {
				if (!graph.isNodeUnneeded(node)) {
					for (Node<LLVMAbstractState> endNode : neededEndNodes) {
						if (graph.hasPath(node, endNode)) {
							continue outer;
						}
					}
					assert false : "GRAPH CONSISTENCY ERROR";
				}
			}
		}
	}
	
	protected void haveAtLeastOneEndState() {
		if(LLVMDebuggingFlags.PERFORM_GRAPH_CONSISTENCY_CHECKS_FOR_TERMINATING_FUNCTIONS) {
			assert !getEndAndErrorNodes().isEmpty(): "GRAPH CONSISTENCY ERROR";
		}
	}
	
	protected void atMostOneReturnStateWithoutGeneralizationPerPairOfProgramPositionAndProgramVariables() {
		Map<Pair<LLVMProgramPosition, Set<String>>, Integer> counts = new LinkedHashMap<>();

		
		//this is no longer the case based on the chosen strategy
		/*for (LLVMFunctionGraph fg : graph.getFunctionGraphTracker().getAllFunctionGraphs()) {
			Set<Node<LLVMAbstractState>> returnStatesNeedingIntersections = 
					fg.getNonGeneralizedReturnNodesPrimitive();

			for (Node<LLVMAbstractState> returnNode : returnStatesNeedingIntersections) {
				LLVMAbstractState returnState = returnNode.getObject();
				
				Pair<LLVMProgramPosition, Set<String>> mapKey = new Pair<>(returnState.getProgramPosition(),returnState.getProgramVariables().keySet());
				
				Integer mapResult = counts.get(mapKey);
				int existingNodesWithSameProgPosAndVariables = mapResult == null ? 0 : mapResult;
				
				assert existingNodesWithSameProgPosAndVariables <= 1;
				
				counts.put(mapKey, existingNodesWithSameProgPosAndVariables+1);
			}

		}*/
	}
	
	//todo each call state reaches at least one return state via most general entry
	
	protected void eachCallStateReachesAtLeastOneReturnState() {
		if(LLVMDebuggingFlags.PERFORM_GRAPH_CONSISTENCY_CHECKS_FOR_TERMINATING_FUNCTIONS) {
			for (LLVMFunctionGraph fg : graph.getFunctionGraphTracker().getAllFunctionGraphs()) {
				Set<Node<LLVMAbstractState>> neededCallNodes = fg.getCallNodesPrimitive();
				Set<Node<LLVMAbstractState>> neededReturnNodes = fg.getNonGeneralizedReturnNodesPrimitive();
				
				callNodeLoop:
				for (Node<LLVMAbstractState> callNode : neededCallNodes) {
					int retNodeReachedCounter = 0;
					
					for (Node<LLVMAbstractState> returnNode : neededReturnNodes) {
						if(fg.getSingleExecutionPathViaMostGeneralEntryStatePrimitive(callNode, returnNode) != null) {
							retNodeReachedCounter++;
						}
					}
					
					
					for(Node<LLVMAbstractState> errorNode : getErrorNodes()) {
						if(graph.hasPath(callNode, errorNode))
							continue callNodeLoop;
					}
					assert  retNodeReachedCounter >= 1: "GRAPH CONSISTENCY ERROR";
				}
					
			}
		}
	}
	
	
	protected void allIntersectionsExist() {
		for (LLVMFunctionGraph fg : graph.getFunctionGraphTracker().getAllFunctionGraphs()) {
			Set<Node<LLVMAbstractState>> neededCallNodes = fg.getCallNodesPrimitive();
			Set<Node<LLVMAbstractState>> neededReturnNodes = fg.getNonGeneralizedReturnNodesPrimitive();

			for (Node<LLVMAbstractState> callNode : neededCallNodes) {
				for (Node<LLVMAbstractState> returnNode : neededReturnNodes) {
					int foundSuitableIntersection = 0;
					
					
					Set<LLVMSEPath> executionPaths = Collections.emptySet();
							
							
					Set<LLVMSEPath> cyclesReachableFromExecutionPath = Collections.emptySet();
					
					if(fg.isPathAgnostic()) {
						LLVMSEPath path = new LLVMSEPath(fg.getSingleExecutionPathViaMostGeneralEntryStatePrimitive(callNode, returnNode),graph);
						executionPaths = Collections.singleton(path);
					} else {
						executionPaths = fg.getExecutionPathsViaMostGeneralEntryState(callNode, returnNode);
						cyclesReachableFromExecutionPath = fg.getAllCyclesReachableFromExecutionPaths(executionPaths);
					}
					
					
					if(fg.hasMatchingFunctionSkipFailureEdgeInGraph(callNode, returnNode, executionPaths, cyclesReachableFromExecutionPath))
						continue;
					
					if(executionPaths.isEmpty())
						continue;
					
					for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getEdges()) {
						if(edge.getObject() instanceof LLVMMethodSkipEdge) {
							LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
							
							if(skipEdge.getIntersectionResult().getCallNode() == callNode && skipEdge.getIntersectionResult().getReturnNode() == returnNode) {
								Node<LLVMAbstractState> intersection = skipEdge.getIntersectionResult().getIntersectedNode();
								assert intersection == edge.getEndNode();
								
								if(fg.isPathAgnostic()) {
									foundSuitableIntersection++;
								} else {
									if(!graph.isNodeUnneeded(intersection)) {
										if(skipEdge.getIntersectionResult().getRespectedExecutionPaths().containsAll(executionPaths)
												&& skipEdge.getIntersectionResult().getRespectedCycles().containsAll(cyclesReachableFromExecutionPath)) {
											foundSuitableIntersection++;
										}
									}
								}
							}
							
							
						}
					}
					
					assert foundSuitableIntersection == 1: "GRAPH CONSISTENCY ERROR";
				}

			}
		}
	}
	

	
	protected void havePredecessors() {
		for(Node<LLVMAbstractState> node : graph.getNodes()) {
			if(graph.isNodeUnneeded(node) 
					|| graph.getRoot() == node 
					|| (graph.getIntersectionHeuristics().isCallAbstractionOrEntryState(node.getObject())
							&& graph.getIntersectionHeuristics().keepSubGraphsForFunctionWhenRemovingUnneededNodesAferGeneralization(node.getObject())))
				continue;
			
			assert !graph.getInEdges(node).isEmpty(): "GRAPH CONSISTENCY ERROR";
		}
	}
	
	protected void outgoingEdgesAreConsistent() {
		for(Node<LLVMAbstractState> node : graph.getNodes()) {
			if(graph.isNodeUnneeded(node) || node.getObject().isEnd())
				continue;
			
			Set<Edge<LLVMEdgeInformation,LLVMAbstractState>> outEdges = graph.getOutEdges(node);
			for(Edge<LLVMEdgeInformation,LLVMAbstractState> edge : outEdges) {
				LLVMEdgeInformation label = edge.getObject();
				if(label instanceof LLVMEvaluationInformation) {
					for(Edge<LLVMEdgeInformation,LLVMAbstractState> otherEdge : outEdges) {
						if(otherEdge.equals(edge))
							continue;
						LLVMEdgeInformation otherLabel = otherEdge.getObject();
						assert otherLabel instanceof LLVMGeneralizationInformation: "GRAPH CONSISTENCY ERROR";
					}
					
				} else if(label instanceof LLVMGeneralizationInformation) {
					for(Edge<LLVMEdgeInformation,LLVMAbstractState> otherEdge : outEdges) {
						if(otherEdge.equals(edge))
							continue;
						LLVMEdgeInformation otherLabel = otherEdge.getObject();
						assert otherLabel instanceof LLVMGeneralizationInformation || otherLabel instanceof LLVMEvaluationInformation: "GRAPH CONSISTENCY ERROR";
					}
					
				} else if(label instanceof LLVMRefinementInformation) {
					for(Edge<LLVMEdgeInformation,LLVMAbstractState> otherEdge : outEdges) {
						if(otherEdge.equals(edge))
							continue;
						LLVMEdgeInformation otherLabel = otherEdge.getObject();
						assert otherLabel instanceof LLVMGeneralizationInformation || otherLabel instanceof LLVMRefinementInformation: "GRAPH CONSISTENCY ERROR";
					}
					
				}
			}
		}
	}
	
	private boolean allSucessorsAreRefinements(Node<LLVMAbstractState> node) {
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getOutEdges(node)) {
			if(!(edge.getObject() instanceof LLVMRefinementInformation))
				return false;
		}
		return true;
	}
	
	private boolean allSucessorsAreGeneralzations(Node<LLVMAbstractState> node) {
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getOutEdges(node)) {
			if(!(edge.getObject() instanceof LLVMInstantiationInformation))
				return false;
		}
		return true;
	}
	
	private Set<Node<LLVMAbstractState>> getErrorNodes() {
			Set<Node<LLVMAbstractState>> errorNodes = new LinkedHashSet<>();
			
			for(Node<LLVMAbstractState> node : graph.getNodes()) {
				if( node.getObject().isErrorState()) {
					errorNodes.add(node);
				}
			}
			
			return errorNodes;
	}
	
	private Set<Node<LLVMAbstractState>> getEndAndErrorNodes() {
		Set<Node<LLVMAbstractState>> endNodes = new LinkedHashSet<>();
		
		for(Node<LLVMAbstractState> node : graph.getNodes()) {
			if(node.getObject().isEnd() || node.getObject().isErrorState() || node.getObject().isInconsistentState()) {
				endNodes.add(node);
			}
		}
		
		return endNodes;
	}
	
	

	
	

	


	
}
