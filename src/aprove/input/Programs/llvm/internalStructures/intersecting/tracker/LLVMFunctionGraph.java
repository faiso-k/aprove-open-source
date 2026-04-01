package aprove.input.Programs.llvm.internalStructures.intersecting.tracker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;


public class LLVMFunctionGraph  {
	
	// without @
	protected final String functionName;

	protected final LLVMIntersectionHeuristics heuristics;

	//A graph containing at least all the edges between the nodes of this graph
	//and additionally the call nodes
	protected final SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> graph;

	// set of nodes with function on bottom, in graph only
	protected final Set<Node<LLVMAbstractState>> nodes;

	// subset of nodes, in graph only.
	//does not contain those return nodes that are copied for failure edges (i.e., have incoming function skip failure edges)
	protected final Set<Node<LLVMAbstractState>> returnNodes;

	// subset of returnNodes, nodes in here must not have outgoing
	// generalization edges.
	protected final Set<Node<LLVMAbstractState>> nonGeneralizedReturnNodes;

	//All cycles in this function graph. null if need to be recalculated
	//cannot be final because we set it to null if we need to recalculate it
	protected Set<LLVMSEPath> allCycles;
	
	//value for a key can be null if it needs to be recalculated
	//may contain entries for exeuction paths no longer in the graph. we rely on the fact that 
	//the map is cleared every once in a while when possible new cycles are added
	protected Map<Set<LLVMSEPath>,Set<LLVMSEPath>> cyclesReachableFromExecutionPath;
	
	//maps (call node,return node) to execution paths via the most general entry state
	//value for a key can be null if it needs to be recalculated
	protected final Map<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>,Set<LLVMSEPath>> executionPathsViaMostGeneralEntryState;

	protected final Map<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>,Pair<Boolean,ArrayList<Node<LLVMAbstractState>>>> callReturnPairsWithPathsViaMostGeneralEntryState;
	
	// subset of nodes, in graph only ("call states" are considered entry nodes,
	// too)
	protected final Set<Node<LLVMAbstractState>> entryNodes;


	//subset of entryNodes, do not have outgoing gen edges
	protected final Set<Node<LLVMAbstractState>> nonGeneralizedEntryNodes;

	// all entry nodes ever seen, even removed ("call abstractions" are
	// considered entry nodes, too)
	protected final Set<Node<LLVMAbstractState>> entryNodeLog;

	// all intersections ever created, even removed (same holds for the call and
	// return nodes in the key, they may be removed, too)
	protected final Map<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>, Set<LLVMIntersectionResult>> intersectionLog;
	
	
	// Only contains a mapping if the call state, return state and intersection
	// are in the graph
	// however, it may not be up to date, i.e., there may be additional
	// executions paths and cycles in the graph
	//the list is sorted from old to new, i.e., the last entry is the most recently created intersection
	//we keep pairs with generalized return nodes in there, we may need them at some point
	protected final Map<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>, List<LLVMIntersectionResult>> intersections;


	// orthogonal from S, in graph only
	protected final Set<Node<LLVMAbstractState>> callNodes;
	
	//all intersection failures for the function this graph covers
	//Only contains a mapping if the call state, return state still exist in the SEGraph. the return node may have been generalized
	protected final Map<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>,Set<Edge<LLVMFunctionSkipFailureEdge,LLVMAbstractState>>> intersectionFailureEdges;
	
	protected final LLVMFunctionGraphSpecificMemoryChangeTracker memoryChangeTracker;
	
	//null means must be recalculated
	protected Map<Node<LLVMAbstractState>, Set<Pair<LLVMSEPath,Integer>>> nodesToCyclesAndPos;
	
	LLVMFunctionGraph(String function, SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph, LLVMIntersectionHeuristics heuristics) {
		this.functionName = function;
		this.graph = graph;
		this.heuristics = heuristics;
		
		this.nodes = new LinkedHashSet<>();
		this.returnNodes = new LinkedHashSet<>();
		this.nonGeneralizedReturnNodes = new LinkedHashSet<>();
		this.callNodes = new LinkedHashSet<>();
		this.entryNodeLog = new LinkedHashSet<>();
		this.entryNodes = new LinkedHashSet<>();
		this.nonGeneralizedEntryNodes = new LinkedHashSet<>();
		
		this.intersectionFailureEdges = new LinkedHashMap<>();
		this.intersections = new LinkedHashMap<>();
		this.intersectionLog = new LinkedHashMap<>();
		
		
		this.executionPathsViaMostGeneralEntryState = new LinkedHashMap<>();
		this.allCycles = null;
		this.nodesToCyclesAndPos = null;
		this.cyclesReachableFromExecutionPath = new LinkedHashMap<>();
		this.callReturnPairsWithPathsViaMostGeneralEntryState = new LinkedHashMap<>();
		
		this.memoryChangeTracker = new LLVMFunctionGraphSpecificMemoryChangeTracker();
	}

	//copy constructor
	protected LLVMFunctionGraph(LLVMFunctionGraph copyMe) {
		this.functionName = copyMe.functionName;

		//We copy the SimpleGraph by creating an induced subgraph: it contains
		//all nodes in this graph (i.e., the nodes with the function at the bottom of the stack which this graph is for)
		//plus the call nodes. This way, all execution paths are preserved
		Set<Node<LLVMAbstractState>> nodesPlusCallNodes = new LinkedHashSet<>(copyMe.getCallNodes());
		nodesPlusCallNodes.addAll(copyMe.getNodes());
		this.graph = copyMe.graph.getSubGraph(nodesPlusCallNodes);


		this.heuristics = copyMe.heuristics;

		this.nodes = new LinkedHashSet<>(copyMe.getNodes());
		this.returnNodes = new LinkedHashSet<>(copyMe.getReturnNodesPrimitive());
		this.nonGeneralizedReturnNodes = new LinkedHashSet<>(copyMe.getNonGeneralizedReturnNodes());
		this.callNodes = new LinkedHashSet<>(copyMe.getCallNodes());
		this.entryNodeLog = new LinkedHashSet<>(copyMe.entryNodeLog);
		this.entryNodes = new LinkedHashSet<>(copyMe.getEntryNodes());
		this.nonGeneralizedEntryNodes = new LinkedHashSet<>(copyMe.getNonGeneralizedEntryNodes());


		this.intersections = new LinkedHashMap<>(copyMe.intersections);
		this.intersectionLog = new LinkedHashMap<>(copyMe.intersectionLog);

		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert copyMe.isIntersectionFailureEdgeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Intersection failure cache inconsistent";
		}
		this.intersectionFailureEdges = new LinkedHashMap<>(copyMe.intersectionFailureEdges);


		this.executionPathsViaMostGeneralEntryState =  new LinkedHashMap<>(copyMe.executionPathsViaMostGeneralEntryState);/*new LinkedHashMap<>();
		for(Node<LLVMAbstractState> callNode : copyMe.getCallNodes() ) {
			for(Node<LLVMAbstractState> returnNode : copyMe.getReturnNodes()) {
				Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode,returnNode);
				Set<LLVMSEPath> paths = copyMe.getExecutionPathsViaMostGeneralEntryState(callNode,returnNode);
				executionPathsViaMostGeneralEntryState.put(key,paths);


			}
		}
		*/
		this.cyclesReachableFromExecutionPath = new LinkedHashMap<>(copyMe.cyclesReachableFromExecutionPath); 
		this.callReturnPairsWithPathsViaMostGeneralEntryState = new LinkedHashMap<>(copyMe.callReturnPairsWithPathsViaMostGeneralEntryState);
 
		this.allCycles = null; //recalculate if needed;
		this.nodesToCyclesAndPos = null; //recalculate if needed
		
		
		this.memoryChangeTracker = new LLVMFunctionGraphSpecificMemoryChangeTracker(copyMe.memoryChangeTracker);

	}
	
	

	//must be called by the graph tracker for all nodes that are added to the SEGraph whose bottommost function is intersectable
	void nodeAdded(Node<LLVMAbstractState> newNode) {
		handleNodeAdded(newNode);
		
		LLVMAbstractState state = newNode.getObject();
		if(getIntersectionHeuristics().isCallAbstractionOrEntryState(state)) {
			handleEntryNodeAdded(newNode);
		}
		
		if(getIntersectionHeuristics().isReturnState(state)) {
			handleReturnNodeAdded(newNode);
		}
		
	}
	
	//must be called by the graph tracker  for all nodes that are removed from the SEGraph whose bottommost function is intersectable
	void nodeRemoved(Node<LLVMAbstractState> existingNode) {
		handleNodeRemoved(existingNode);
		
		LLVMAbstractState state = existingNode.getObject();
		if(getIntersectionHeuristics().isCallAbstractionOrEntryState(state)) {
			handleEntryNodeRemoved(existingNode);
		}
		
		if(getIntersectionHeuristics().isReturnState(state)) {
			handleReturnNodeRemoved(existingNode);
		}
	}
	
	//must be called by the graph tracker for all edges added to the graph where either the start or end state is in this function graph
	void edgeAdded(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		handleAddedEdge(start, end, label);
	}
	
	//must be called by the graph tracker  for all edges removed from the graph where either the start or end state is in this function graph
	void edgeRemoved(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		handleRemovedEdge(start, end, label);
	}
	

	
	
	//must be called for all call nodes added to the segraph whose topmost function is the one this function graph manages
	void callNodeAdded(Node<LLVMAbstractState> callNode) {
		handleCallNodeAdded(callNode);
	}
	
	//must be called for all call nodes removed from the segraph whose topmost function is the one this function graph manages
	void callNodeRemoved(Node<LLVMAbstractState> callNode) {
		handleCallNodeRemoved(callNode);
	}
	
	//must be called for all intersections added to the segraph whose topmost function is the one this function graph manages
	void intersectionAdded(LLVMIntersectionResult intersectionRes) {
		handleIntersectionAdded(intersectionRes);
	}
	
	
	//must be called for all intersections removed from the segraph whose topmost function is the one this function graph manages
	void intersectionRemoved(LLVMIntersectionResult intersectionRes) {
		handleIntersectionRemoved(intersectionRes);
	}
	



	
	
	public LLVMIntersectionResult getMostRecentIntersection(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isIntersectionsCacheConsistent() : "GRAPH CONSISTENCY ERROR: intersection cache not consistent";
		}

		Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode, returnNode);
		List<LLVMIntersectionResult> intersectionsForPair = intersections.get(key);
		
		if(intersectionsForPair == null || intersectionsForPair.isEmpty())
			return null;
		
		return intersectionsForPair.get(intersectionsForPair.size()-1);
	}
	
	
	//uses the mapping mostRecentIntersections, but returns null if the result in the map respects something (cycle, execution path) that is not in the graph
	//any more
	//however, the returned intersection may respect less
	public LLVMIntersectionResult getMostRecentIntersectionRespectingPresentPathsAndCycles(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		LLVMIntersectionResult mostRecentIntersection = getMostRecentIntersection(callNode,returnNode);

		if(mostRecentIntersection == null) {
			return null;
		}
		
		Set<LLVMSEPath> respectedExecutionPaths = mostRecentIntersection.getRespectedExecutionPaths();

		Set<LLVMSEPath> respectedCycles = mostRecentIntersection.getRespectedCycles();

		Set<LLVMSEPath> currentExecutionPathsInGraph = getExecutionPathsViaMostGeneralEntryState(callNode,returnNode);
		Set<LLVMSEPath> currentCycles = getAllCyclesReachableFromExecutionPaths(currentExecutionPathsInGraph);

		if(currentExecutionPathsInGraph.containsAll(respectedExecutionPaths) && currentCycles.containsAll(respectedCycles)) {
			return mostRecentIntersection;
		} else {
			return null;
		}
		

		
		
	}
	
	private boolean isPrefix(List<Node<LLVMAbstractState>> path, List<Node<LLVMAbstractState>> potentialPrefix) {
		for(int i = 0; i < potentialPrefix.size(); i++) {
			if(!path.get(i).equals(potentialPrefix.get(i)))
				return false;
		}
		return true;
	}
	
	
	public Set<Node<LLVMAbstractState>> getCallNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isCallNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Function graph call nodes out of sync";
		}
		return callNodes;
	}

	public Set<Node<LLVMAbstractState>> getReturnNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isReturnNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Function graph return nodes out of sync";
		}
		return returnNodes;
	}

	public Set<Node<LLVMAbstractState>> getEntryNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isEntryNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Function graph entry nodes out of sync";
		}
		return entryNodes;
	}

	public Set<Node<LLVMAbstractState>> getNonGeneralizedEntryNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isNonGeneralizedEntryNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Function graph non-generalized entry nodes out of sync";
		}
		return nonGeneralizedEntryNodes;
	}
	
	
	public Set<Node<LLVMAbstractState>> getNonGeneralizedReturnNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isNonGeneralizedReturnNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Function graph non-generalized return nodes out of sync";
		}
		return nonGeneralizedReturnNodes;
	}

	//does not return paths containg an instantiation edge between intersections
	public Set<LLVMSEPath> getExecutionPathsViaMostGeneralEntryState(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		if(isPathAgnostic()) {
			throw new IllegalStateException("This function graph does not care about paths. Do not ask for them");
		}
		
		Set<LLVMSEPath> cachedExecutionPaths = executionPathsViaMostGeneralEntryState.get(new Pair<>(callNode,returnNode));
		if(cachedExecutionPaths == null) {
			cachedExecutionPaths = getExecutionPathsViaMostGeneralEntryStatePrimitive(callNode, returnNode);
			executionPathsViaMostGeneralEntryState.put(new Pair<>(callNode,returnNode), cachedExecutionPaths);
		} else {
			if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
				assert isExecutionPathCacheConsistent() : "GRAPH CONSISTENCY ERROR: Execution Path cache out of sync";
			}
		}
		return cachedExecutionPaths;
	}
	
	public ArrayList<Node<LLVMAbstractState>> getSingleExecutionPathViaMostGeneralEntryState(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		Pair<Boolean,ArrayList<Node<LLVMAbstractState>>> cacheResult = callReturnPairsWithPathsViaMostGeneralEntryState.get(new Pair<>(callNode,returnNode));
		if(cacheResult == null) {
			ArrayList<Node<LLVMAbstractState>> path = getSingleExecutionPathViaMostGeneralEntryStatePrimitive(callNode, returnNode);
			callReturnPairsWithPathsViaMostGeneralEntryState.put(new Pair<>(callNode,returnNode), new Pair<>(path != null, path));
			return path;
		} else {
			if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
				assert isExecutionPathExistenceCacheConsistent() : "GRAPH CONSISTENCY ERROR: Execution Path cache out of sync";
			}
		}
		return cacheResult.y;
	}

	
	
	public Set<LLVMSEPath> getAllCycles() {
		if(isPathAgnostic()) {
			throw new IllegalStateException("This function graph does not care about paths. Do not ask for them");
		}
		
		if(allCycles == null) {
			allCycles = getAllCyclesPrimitive();
		} else {
			if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
				assert isCycleCacheConsistent() : "GRAPH CONSISTENCY ERROR: Cycle cache out of sync";
			}
		}
		return allCycles;
	}
	
	//does not guarantee that the returned cycles are actually reachable, but all reachable ones are returned
	public Set<LLVMSEPath> getAllCyclesReachableFromExecutionPaths(Set<LLVMSEPath> executionPaths) {
		if(isPathAgnostic()) {
			throw new IllegalStateException("This function graph does not care about paths. Do not ask for them");
		}
		
		Set<LLVMSEPath> cachedExecutionPaths = cyclesReachableFromExecutionPath.get(executionPaths);
		if(cachedExecutionPaths == null) {
			cachedExecutionPaths = getAllCyclesReachableFromExecutionPathsPrimitive(executionPaths);
			cyclesReachableFromExecutionPath.put(executionPaths, cachedExecutionPaths);
		} else {
			if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
				assert isExecutionPathCacheConsistent() : "GRAPH CONSISTENCY ERROR: Execution Path cache out of sync";
			}
		}
		return cachedExecutionPaths;
	}

	//Do not modify!
	public SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> getGraph() {
		return graph;
	}

	public Set<Node<LLVMAbstractState>> getNodes() {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isNodeCacheConsistent() : "GRAPH CONSISTENCY ERROR : Node cache not consistent";
		}
		return nodes;
	}
	
	public boolean hasMatchingFunctionSkipFailureEdgeInGraph(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, Set<LLVMSEPath> executionPaths, Set<LLVMSEPath> cyclesReachableFromExecutionPath) {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isIntersectionFailureEdgeCacheConsistent() : "GRAPH CONSISTENCY ERROR: Cache for intersection failures out of sync";
		}
		Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode,returnNode);
		Set<Edge<LLVMFunctionSkipFailureEdge,LLVMAbstractState>> failures = intersectionFailureEdges.getOrDefault(key,Collections.emptySet());

		if(isPathAgnostic()) {
			return !failures.isEmpty();
		} else {
			//If the intersection failed already when considering just a superset of the paths and cycles, 
			//it would in particular fail when considering fewer execution paths and cycles
			for(Edge<LLVMFunctionSkipFailureEdge,LLVMAbstractState> failureEdge : failures) {
				LLVMFunctionSkipFailureEdge label = failureEdge.getObject();
				if(label.getRespectedPaths().containsAll(executionPaths) && label.getRespectedCycles().containsAll(cyclesReachableFromExecutionPath)) {
					return true;
				}
			}	
		}
		return false;
	}
	
	
	
	public Set<LLVMIntersectionResult> getIntersectionsWithReturnNode(Node<LLVMAbstractState> returnNode) {
		if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
			assert isIntersectionsCacheConsistent() : "GRAPH CONSISTENCY ERROR: Intersection cache not consistent";
		}

		Set<LLVMIntersectionResult> result = new LinkedHashSet<>();
		for(Map.Entry<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>,List<LLVMIntersectionResult>> e : intersections.entrySet()) {
			if(e.getKey().y == returnNode) {
				result.addAll(e.getValue());
			}
		}
		return result;
	}
	
	
	

	
	
	public Node<LLVMAbstractState> getCallAbstraction(Node<LLVMAbstractState> callNode) {
		Set<Node<LLVMAbstractState>> foundCallAbstractions = new LinkedHashSet<>();
		
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> outEdge : graph.getOutEdges(callNode)) {
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
	
	


	//here, call abstractions are considered entry nodes, too
	public Node<LLVMAbstractState> getMostGeneralEntryNode(Node<LLVMAbstractState> entryNode) {
		List<Node<LLVMAbstractState>> path = getPathToMostGeneralEntryNode(entryNode);
		return path.get(path.size()-1);
	}
	
	public List<Node<LLVMAbstractState>> getPathToMostGeneralEntryNode(Node<LLVMAbstractState> entryNode) {
		List<Node<LLVMAbstractState>> path = new ArrayList<>();
		path.add(entryNode);
		
		boolean foundGeneralization = false;
		
		do  {
			foundGeneralization = false;
			
			if(Globals.useAssertions) {
				assert outgoingGeneralizationEdgeCount(entryNode) <= 1 : "GRAPH CONSISTENCY ERROR: Entry node has more than one generalization";
			}
			
			for(Edge<LLVMEdgeInformation,LLVMAbstractState> e : graph.getOutEdges(entryNode)) {
				if(e.getObject() instanceof LLVMInstantiationInformation) {
					entryNode = e.getEndNode();
					path.add(entryNode);
					foundGeneralization = true;
					break; 
				}
			}

		} while(foundGeneralization);
		return path;
	}
	
	public ArrayList<Node<LLVMAbstractState>> getPathToMostGeneralEntryNodeFromCallNode(Node<LLVMAbstractState> callNode) {
		Node<LLVMAbstractState> callAbstraction = getCallAbstraction(callNode);
		if(callAbstraction == null)
			return null;
		
		ArrayList<Node<LLVMAbstractState>> resultPath = new ArrayList<>();
		resultPath.add(callNode);
		resultPath.addAll(getPathToMostGeneralEntryNode(callAbstraction));
		return resultPath;
		
	}
	
	
	//here, generalization also includes instantiation edges
	public int outgoingGeneralizationEdgeCount(Node<LLVMAbstractState> node) {
		return (int) graph.getOutEdges(node)
				.stream()
				.filter(e -> e.getObject() instanceof LLVMInstantiationInformation)
				.count();

	}
	
	
	
	
	private void handleNodeAdded(Node<LLVMAbstractState> node) {
		if(Globals.useAssertions) {
			assert !nodes.contains(node) : "GRAPH CONSISTENCY ERROR: about to add node to FG that is already there";
		}
		nodes.add(node);
	}
	
	private void handleNodeRemoved(Node<LLVMAbstractState> node) {
		if(Globals.useAssertions) {
			assert nodes.contains(node) : "GRAPH CONSISTENCY ERROR: about to remove node from FG that is not there";
		}
		nodes.remove(node);
		getMemoryChangeTracker().removedNodeFromGraph(node);
	}
	
	private void handleAddedEdge(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		if(nonGeneralizedReturnNodes.contains(start) && label instanceof LLVMInstantiationInformation) {
			nonGeneralizedReturnNodes.remove(start);
		}

		if(nonGeneralizedEntryNodes.contains(start) && label instanceof LLVMInstantiationInformation) {
			nonGeneralizedEntryNodes.remove(start);
			
			//we have generalized an entry node
			executionPathsViaMostGeneralEntryState.clear();
			callReturnPairsWithPathsViaMostGeneralEntryState.clear();
		}


		if(label instanceof LLVMFunctionSkipFailureEdge) {
			if(returnNodes.contains(end)) {
				returnNodes.remove(end);
				nonGeneralizedReturnNodes.remove(end);
			}
			String callStateFunction = start.getObject().getCurrentFunction();
			if(callStateFunction.equals(functionName)) {
				//If this does not hold, the failure edge is for a call state of a different function
				//We were notified about the edge because the bottommost function in the stack must
				//be the function this function graph deals with
				
				LLVMFunctionSkipFailureEdge failureEdge = (LLVMFunctionSkipFailureEdge) label;
				Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key =
						new Pair<>(start,failureEdge.getReturnNode());
				
				Set<Edge<LLVMFunctionSkipFailureEdge,LLVMAbstractState>> failureEdgesForPair =
						intersectionFailureEdges.computeIfAbsent(key, k -> new LinkedHashSet<>());
				
				failureEdgesForPair.add(new Edge<>(start,end,failureEdge));
			}
		}
		
		//Lets check if this new edge could have changed the cycles and execution paths within this function graph:
		if(nodes.contains(end)
				&& (graph.getOut(end).stream().anyMatch(n -> nodes.contains(n))
					|| returnNodes.contains(end))) {
			allCycles = null;
			nodesToCyclesAndPos = null;
			executionPathsViaMostGeneralEntryState.clear();
			callReturnPairsWithPathsViaMostGeneralEntryState.clear();
			cyclesReachableFromExecutionPath.clear();
		}
	}
	
	private void handleRemovedEdge(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		if(returnNodes.contains(start) && graph.contains(start) && label instanceof LLVMInstantiationInformation) {
			if(Globals.useAssertions) {
					assert graph.getOutEdges(start)
							.stream()
							.allMatch(e -> !(e.getObject() instanceof LLVMInstantiationInformation)) :
							"GRAPH CONSISTENCY ERROR: Return node had multiple outgoing gen. edges";
			}
			nonGeneralizedReturnNodes.add(start);
		}

		if(entryNodes.contains(start) && graph.contains(start) && label instanceof LLVMInstantiationInformation) {
			if(Globals.useAssertions) {
				assert graph.getOutEdges(start)
						.stream()
						.allMatch(e -> !(e.getObject() instanceof LLVMInstantiationInformation)) :
						"GRAPH CONSISTENCY ERROR: Entry node had multiple outgoing gen. edges";
			}
			nonGeneralizedEntryNodes.add(start);
		}

		//The following is only needed to satisfy some consistency checks,
		//We can assume that removing a LLVMFunctionSkipFailureEdge means that the end node will be removed afterwards, too
		if(label instanceof LLVMFunctionSkipFailureEdge) {
			if(getIntersectionHeuristics().isReturnState(end.getObject()) && end.getObject().getCurrentFunction().equals(functionName)) {
				returnNodes.add(end);
				if (outgoingGeneralizationEdgeCount(end) == 0)
					nonGeneralizedReturnNodes.add(end);
			}
		}
		
		//Lets check if this removed edge could have changed the cycles and execution paths within this function graph:
		if(nodes.contains(end)) {
			allCycles = null;
			nodesToCyclesAndPos = null;
			executionPathsViaMostGeneralEntryState.clear();
			callReturnPairsWithPathsViaMostGeneralEntryState.clear();
			cyclesReachableFromExecutionPath.clear();
		}
	}
	
	
	private void handleEntryNodeAdded(Node<LLVMAbstractState> node) {
		entryNodeLog.add(node);
		entryNodes.add(node);

		//when added, cannot have outgoing edges, yet
		nonGeneralizedEntryNodes.add(node);
	}
	
	private void handleEntryNodeRemoved(Node<LLVMAbstractState> node) {
		entryNodes.remove(node);
		nonGeneralizedEntryNodes.remove(node); //may not necessarily been in there
	}
	
	private void handleReturnNodeAdded(Node<LLVMAbstractState> node) {
		returnNodes.add(node);
		
		//The node added handler is called before any edge is added
		//Thus, the node cannot have an outgoing generalization edge, yet
		nonGeneralizedReturnNodes.add(node);
	}
	
	private void handleReturnNodeRemoved(Node<LLVMAbstractState> node) {
		returnNodes.remove(node);
		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt = executionPathsViaMostGeneralEntryState.keySet().iterator();
		while(keyIt.hasNext()) {
			if(keyIt.next().y == node) {
				keyIt.remove();
			}
		}

		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt2 = intersectionFailureEdges.keySet().iterator();
		while(keyIt2.hasNext()) {
			if(keyIt2.next().y == node) {
				keyIt2.remove();
			}
		}

		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt3 = intersections.keySet().iterator();
		while(keyIt3.hasNext()) {
			if(keyIt3.next().y == node) {
				keyIt3.remove();
			}
		}
		
		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt4 = callReturnPairsWithPathsViaMostGeneralEntryState.keySet().iterator();
		while(keyIt4.hasNext()) {
			if(keyIt4.next().y == node) {
				keyIt4.remove();
			}
		}

		nonGeneralizedReturnNodes.remove(node); //may not have been in there
	}
	
	private void handleIntersectionAdded(LLVMIntersectionResult intersectionRes) {
		Node<LLVMAbstractState> callNode = intersectionRes.getCallNode();
		Node<LLVMAbstractState> returnNode = intersectionRes.getReturnNode();
		Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode, returnNode);
		
		Set<LLVMIntersectionResult> curIntersectionLog = intersectionLog.computeIfAbsent(key, k -> new LinkedHashSet<>());
		
		List<LLVMIntersectionResult> curIntersections = intersections.computeIfAbsent(key, k -> new ArrayList<>());
		
		curIntersectionLog.add(intersectionRes);
		curIntersections.add(intersectionRes);
		
	}
	
	private void handleIntersectionRemoved(LLVMIntersectionResult intersectionRes) {
		Node<LLVMAbstractState> callNode = intersectionRes.getCallNode();
		Node<LLVMAbstractState> returnNode = intersectionRes.getReturnNode();
		Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode, returnNode);
		
		List<LLVMIntersectionResult> curIntersections = intersections.get(key);
		if(curIntersections == null) {
			if(Globals.useAssertions) {
				assert !graph.contains(callNode) || !graph.contains(returnNode);
			}
		} else {
			curIntersections.remove(intersectionRes);
		}
	}
	
	private void handleCallNodeAdded(Node<LLVMAbstractState> node) {
		callNodes.add(node);
	}
	

	
	private void handleCallNodeRemoved(Node<LLVMAbstractState> node) {
		callNodes.remove(node);

		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt = executionPathsViaMostGeneralEntryState.keySet().iterator();
		while(keyIt.hasNext()) {
			if(keyIt.next().x == node) {
				keyIt.remove();
			}
		}

		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt2 = intersectionFailureEdges.keySet().iterator();
		while(keyIt2.hasNext()) {
			if(keyIt2.next().x == node) {
				keyIt2.remove();
			}
		}

		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt3 = intersections.keySet().iterator();
		while(keyIt3.hasNext()) {
			if(keyIt3.next().x == node) {
				keyIt3.remove();
			}
		}
		
		Iterator<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> keyIt4 = callReturnPairsWithPathsViaMostGeneralEntryState.keySet().iterator();
		while(keyIt4.hasNext()) {
			if(keyIt4.next().x == node) {
				keyIt4.remove();
			}
		}
	}
	
	public Set<Pair<LLVMSEPath,Integer>> getCyclesAndPositionsOnThemForNode(Node<LLVMAbstractState> node) {
		Map<Node<LLVMAbstractState>, Set<Pair<LLVMSEPath,Integer>>> map = getNodesToCyclesAndPos();
		
		Set<Pair<LLVMSEPath,Integer>> mapResult = map.get(node);
		return mapResult == null ? Collections.emptySet() : mapResult;
	}
	
	public Map<Node<LLVMAbstractState>, Set<Pair<LLVMSEPath,Integer>>> getNodesToCyclesAndPos() {
		if(nodesToCyclesAndPos == null) {
			nodesToCyclesAndPos = getNodesToCyclesAndPosPrimitive();
		} else {
			if(Globals.useAssertions && LLVMDebuggingFlags.PERFORM_SLOW_FUNCTION_GRAPH_CONSISTENCY_CHECKS) {
				assert isNodeToCyclesAndPosCacheConsistent() : "GRAPH CONSISTENCY ERROR: node to cycles and pos cache not consistent";
			}
			
		}
		return nodesToCyclesAndPos;
	}
	
	
	private LLVMIntersectionHeuristics getIntersectionHeuristics() {
		return heuristics;
	}
	
	/* Methods for consistency checks below */
	
	public Set<Node<LLVMAbstractState>> getCallNodesPrimitive() {
		Predicate<? super Node<LLVMAbstractState>> isCallStateOfGivenFunction = 
				node -> (getIntersectionHeuristics().isCallState(node.getObject()) && node.getObject().getCurrentFunction().equals(functionName));
		
		return graph.getNodes()
				.stream()
				.filter(isCallStateOfGivenFunction)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public  Set<Node<LLVMAbstractState>> getReturnNodesPrimitive() {
		Predicate<? super Node<LLVMAbstractState>> isReturnStateOfGivenFunction = 
				node -> (getIntersectionHeuristics().isReturnState(node.getObject()) && node.getObject().getCurrentFunction().equals(functionName));

		Predicate<? super Node<LLVMAbstractState>> hasNoIncomingFunctionSkipFailureEdge = node -> (graph
				.getInEdges(node)
				.stream()
				.noneMatch(edge -> (edge.getObject() instanceof LLVMFunctionSkipFailureEdge)));

		return graph.getNodes().stream()
				.filter(isReturnStateOfGivenFunction)
				.filter(hasNoIncomingFunctionSkipFailureEdge)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public  Set<Node<LLVMAbstractState>> getNonGeneralizedReturnNodesPrimitive() {
		Predicate<? super Node<LLVMAbstractState>> hasNoGeneralization = 
				node -> (graph.getOutEdges(node)
						.stream()
						.noneMatch(edge -> (edge.getObject() instanceof LLVMInstantiationInformation)));
		
		
		return getReturnNodesPrimitive()
				.stream()
				.filter(hasNoGeneralization)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public Set<LLVMSEPath> getAllCyclesPrimitive() {
		//TODO would it be more efficient to run on the original graph, but use a different edge filter?
		SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> inducedSubGraph = graph.getSubGraph(getNodes());
		List<ArrayList<Node<LLVMAbstractState>>> cycles = GraphAlgorithms.<LLVMAbstractState,LLVMEdgeInformation>getCycles(inducedSubGraph,doNotUseCallAbstractionEdges);
		return cycles
				.stream()
				.map(list -> new LLVMSEPath(list,null)) //TODO: passing null here as the SEGraph. ok?
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	public Set<Edge<LLVMEdgeInformation,LLVMAbstractState>> getIntersectionFailureEdgesPrimitive(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		Predicate<? super Edge<LLVMEdgeInformation,LLVMAbstractState>> failureEdgesForGivenPair = 
				edge -> edge.getStartNode() == callNode &&
						edge.getObject() instanceof LLVMFunctionSkipFailureEdge &&
						((LLVMFunctionSkipFailureEdge) edge.getObject()).getReturnNode() == returnNode;
		
		
		return graph.getEdges()
			.stream()
			.filter(failureEdgesForGivenPair)
			.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	
	public List<LLVMIntersectionResult> getIntersectionsPrimitive(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		List<LLVMIntersectionResult> intersections = new ArrayList<>();
		
		Set<Edge<LLVMEdgeInformation,LLVMAbstractState>> skipEdgesForCallNode = 
				graph.getEdges()
				.stream()
				.filter(e -> ((e.getObject() instanceof LLVMMethodSkipEdge) && (e.getStartNode() == callNode)))
				.collect(Collectors.toCollection(LinkedHashSet::new));
		
		for(Edge<LLVMEdgeInformation,LLVMAbstractState> edge : skipEdgesForCallNode) {
			LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
			if(skipEdge.getIntersectionResult().getReturnNode() == returnNode) {
				intersections.add(skipEdge.getIntersectionResult());
			}
			
		}
		
		//sort by node IDs in asecending order, which implies that nodes are returned in order of creation (newest one last in list)
		Collections.sort(intersections, new Comparator<LLVMIntersectionResult>() {
		    public int compare(LLVMIntersectionResult one, LLVMIntersectionResult other) {
		        return one.getIntersectedNode().getNodeNumber() - other.getIntersectedNode().getNodeNumber();
		    }
		});
		
		
		return intersections;		
	}
	

	public Set<LLVMSEPath> getAllCyclesReachableFromExecutionPathsPrimitive(Set<LLVMSEPath> executionPaths) {
		Set<LLVMSEPath> result = new LinkedHashSet<>();
		Set<LLVMSEPath> allCycles = getAllCycles();
		Set<Node<LLVMAbstractState>> reachableNodes = new LinkedHashSet<>();
		executionPaths.forEach(reachableNodes::addAll);
		
		boolean changed = false;
		do {
			changed = false;
			for(LLVMSEPath cycle : allCycles) {
				if(cycle.stream().anyMatch(node -> reachableNodes.contains(node))) {
					changed |= result.add(cycle);
					reachableNodes.addAll(cycle);
				}
			}
			
		} while(changed);
		return result;
	}
	
	
	//does not return execution paths via 
	public Set<LLVMSEPath> getExecutionPathsViaMostGeneralEntryStatePrimitive(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		//By definition of execution paths, the only allowed call abstraction edge is the one from the call node to its call abstraction,
		//which is the first edge in any execution path.
		//Since we search from the entry node on (i.e., a succesor of the call abstraction), we ignore all subseqent call abstraction edges
		//In addition, we ignore <code>LLVMIntersectionInstantiationInformation</code>. Such edges indicate that a path should not be considered an execution path,
		//because it did not yield different results as compared to another path
		EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> ef = new EdgeFilter<LLVMEdgeInformation, LLVMAbstractState>() {
			@Override
            public boolean selectEdge(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest, LLVMEdgeInformation label) {
                return !((label instanceof LLVMCallAbstractionEdge) || (label instanceof LLVMIntersectionInstantiationInformation));
            }
		};
		
		Node<LLVMAbstractState> callAbstraction = getCallAbstraction(callNode);
		if(callAbstraction == null)
			return Collections.emptySet();


		List<Node<LLVMAbstractState>> pathFromCallAbstractionToMostGeneralEntryState = getPathToMostGeneralEntryNode(callAbstraction);
		Node<LLVMAbstractState> mostGeneralEntryState =  getMostGeneralEntryNode(callAbstraction);
		Set<List<Node<LLVMAbstractState>>> allPathsFromEntryNodeOn = graph.getAllPaths(mostGeneralEntryState, returnNode,ef);
		
		Set<LLVMSEPath> executionPaths = new LinkedHashSet<>();
		for(List<Node<LLVMAbstractState>> pathFromEntryNode : allPathsFromEntryNodeOn) {
			//start add call node
			LLVMSEPath executionPath = new LLVMSEPath(Collections.singletonList(callNode), this.getGraph()); //TODO setting the SEG to null here. ok?
			
			//add the path from call node to most general entry node
			executionPath.addAll(pathFromCallAbstractionToMostGeneralEntryState);

			//remove the last node in the path so far, because it will be added again below
			executionPath.remove(executionPath.size()-1);
			
			//add path from entry node to return node
			executionPath.addAll(pathFromEntryNode);
			
			executionPaths.add(executionPath);
			
		}
		
		return executionPaths;
	}
	
	public ArrayList<Node<LLVMAbstractState>> getSingleExecutionPathViaMostGeneralEntryStatePrimitive(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		//By definition of execution paths, the only allowed call abstraction edge is the one from the call node to its call abstraction,
		//which is the first edge in any execution path.
		//Since we search from the entry node on (i.e., a succesor of the call abstraction), we ignore all subseqent call abstraction edges
		//In addition, we ignore <code>LLVMIntersectionInstantiationInformation</code>. Such edges indicate that a path should not be considered an execution path,
		//because it did not yield different results as compared to another path
		EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> ef = new EdgeFilter<LLVMEdgeInformation, LLVMAbstractState>() {
			@Override
            public boolean selectEdge(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest, LLVMEdgeInformation label) {
                return !((label instanceof LLVMCallAbstractionEdge) || (label instanceof LLVMIntersectionInstantiationInformation));
            }
		};
		
		Node<LLVMAbstractState> callAbstraction = getCallAbstraction(callNode);
		if(callAbstraction == null)
			return null;


		Node<LLVMAbstractState> mostGeneralEntryState =  getMostGeneralEntryNode(callAbstraction);
		
		LinkedList<Node<LLVMAbstractState>> path =  getGraph().getPath(mostGeneralEntryState, returnNode, ef);
		if(path == null)
			return null;
		else {
			List<Node<LLVMAbstractState>> pathToMostGeneralEntryNode = getPathToMostGeneralEntryNodeFromCallNode(callNode);
			ArrayList<Node<LLVMAbstractState>> result = new ArrayList<>();
			for(int i = 0; i < pathToMostGeneralEntryNode.size() - 1; i++) {
				result.add(pathToMostGeneralEntryNode.get(i));
			}
			result.addAll(path);
			return result;
		}
	}
	
	public Map<Node<LLVMAbstractState>, Set<Pair<LLVMSEPath,Integer>>> getNodesToCyclesAndPosPrimitive() {
		Map<Node<LLVMAbstractState>, Set<Pair<LLVMSEPath,Integer>>> map = new LinkedHashMap<>();
		Set<LLVMSEPath> allCycles = getAllCycles();
		
		for(LLVMSEPath cycle : allCycles) {
			// -1 because the last node in the cycle is the same as the first one
			for(int index = 0; index < cycle.size() - 1; index++) {
				Node<LLVMAbstractState> node = cycle.get(index);
				
				Set<Pair<LLVMSEPath,Integer>> existingPairs = map.computeIfAbsent(node, n -> new LinkedHashSet<>());
				
				existingPairs.add(new Pair<>(cycle,index));
			}
		}
		
		return map;
	}

	public Set<Node<LLVMAbstractState>> getEntryNodesPrimitive() {
		return graph.getNodes()
				.stream()
				.filter(n -> getIntersectionHeuristics().isCallAbstractionOrEntryState(n.getObject()) && n.getObject().getCurrentFunction().equals(functionName))
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}

	public Set<Node<LLVMAbstractState>> getNonGeneralizedEntryNodesPrimitive() {
		return getEntryNodesPrimitive()
				.stream()
				.filter(n -> outgoingGeneralizationEdgeCount(n) == 0)
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}

	
	public Set<Node<LLVMAbstractState>> getNodesPrimitive() {
		return graph.getNodes()
				.stream()
				.filter(n -> n.getObject().getBottommostFunctionInStack().equals(functionName))
				.collect(Collectors.toCollection(LinkedHashSet::new));
	}
	
	private boolean isCycleCacheConsistent() {
		return getAllCyclesPrimitive().equals(allCycles);
	}
	
	private boolean isNodeCacheConsistent() {
		return getNodesPrimitive().equals(nodes);
	}
	
	private boolean isCallNodeCacheConsistent() {
		return getCallNodesPrimitive().equals(callNodes);
	}
	
	private boolean isReturnNodeCacheConsistent() {
		return getReturnNodesPrimitive().equals(returnNodes);
	}
	
	private boolean isNonGeneralizedReturnNodeCacheConsistent() {
		return getNonGeneralizedReturnNodesPrimitive().equals(nonGeneralizedReturnNodes);
	}

	private boolean isEntryNodeCacheConsistent() {
		return getEntryNodesPrimitive().equals(entryNodes);
	}

	private boolean isNonGeneralizedEntryNodeCacheConsistent() {
		return getNonGeneralizedEntryNodesPrimitive().equals(nonGeneralizedEntryNodes);
	}
	
	private boolean isNodeToCyclesAndPosCacheConsistent() {
		return getNodesToCyclesAndPosPrimitive().equals(nodesToCyclesAndPos);
	}


	
	private boolean isIntersectionFailureEdgeCacheConsistent() {
		Set<Node<LLVMAbstractState>> callNodes = getCallNodesPrimitive();
		Set<Node<LLVMAbstractState>> returnNodes = getReturnNodesPrimitive();
		
		boolean consistent = true;
		for(Node<LLVMAbstractState> callNode : callNodes) {
			for(Node<LLVMAbstractState> returnNode : returnNodes) {
				Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode,returnNode);
				consistent &= compareCollectionsNullOkForFirst(intersectionFailureEdges.get(key),getIntersectionFailureEdgesPrimitive(callNode,returnNode));
			}
		}
		
		for(Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key : intersectionFailureEdges.keySet()) {
			consistent &= callNodes.contains(key.x) && returnNodes.contains(key.y);
		}
		
		return consistent;
	}
	
	private boolean isIntersectionsCacheConsistent() {
		Set<Node<LLVMAbstractState>> callNodes = getCallNodesPrimitive();
		//Set<Node<LLVMAbstractState>> nonGeneralizedReturnNodes = getNonGeneralizedReturnNodesPrimitive();
		Set<Node<LLVMAbstractState>> returnNodes = getReturnNodesPrimitive();
		
		boolean consistent = true;
		for(Node<LLVMAbstractState> callNode : callNodes) {
			for(Node<LLVMAbstractState> returnNode : returnNodes) {
				Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode,returnNode);
				consistent &= compareCollectionsNullOkForFirst(intersections.get(key),getIntersectionsPrimitive(callNode,returnNode));
			}
		}
		
		for(Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key : intersections.keySet()) {
			consistent &= callNodes.contains(key.x) && returnNodes.contains(key.y);
		}
		
		return consistent;
	}
	

	
	private boolean isExecutionPathCacheConsistent() {
		Set<Node<LLVMAbstractState>> callNodes = getCallNodesPrimitive();
		Set<Node<LLVMAbstractState>> nonGeneralizedReturnNodes = getNonGeneralizedReturnNodesPrimitive();
		Set<Node<LLVMAbstractState>> returnNodes = getReturnNodesPrimitive();
				
		boolean consistent = true;
		for(Node<LLVMAbstractState> callNode : callNodes) {
			for(Node<LLVMAbstractState> returnNode : nonGeneralizedReturnNodes) {
				Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key = new Pair<>(callNode,returnNode);
				Set<LLVMSEPath> executionPathsFromCache = executionPathsViaMostGeneralEntryState.get(key);
				if(executionPathsFromCache != null) {
					consistent &= getExecutionPathsViaMostGeneralEntryStatePrimitive(callNode, returnNode).equals(executionPathsFromCache);
				}
			}
		}
		
		for(Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> key : executionPathsViaMostGeneralEntryState.keySet()) {
			consistent &= callNodes.contains(key.x) && returnNodes.contains(key.y);
		}
		
		return consistent;
	}
	
	private boolean isExecutionPathExistenceCacheConsistent() {
		boolean consistent = true;
		for(Map.Entry<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>, Pair<Boolean,ArrayList<Node<LLVMAbstractState>>>> e : callReturnPairsWithPathsViaMostGeneralEntryState.entrySet()) {
			if(e.getValue().x) {
				//Check if path still exists in graph:
				ArrayList<Node<LLVMAbstractState>> cachedExecutionPath = e.getValue().y;
				for(int i = 0; i < cachedExecutionPath.size() - 1; i++) {
					Node<LLVMAbstractState> curNode = cachedExecutionPath.get(i);
					Node<LLVMAbstractState> nextNode = cachedExecutionPath.get(i+1);
					
					consistent &=  (getGraph().getEdge(curNode, nextNode) != null);
				}
			} else {
				consistent &= getSingleExecutionPathViaMostGeneralEntryStatePrimitive(e.getKey().x, e.getKey().y) == null;
			}
			
		}
		return consistent;
		
	}
	
	private boolean isReachableCycleCacheConsistent() {
		boolean consistent = true;
		for(Map.Entry<Set<LLVMSEPath>, Set<LLVMSEPath>> e: cyclesReachableFromExecutionPath.entrySet()) {
			consistent &= getAllCyclesReachableFromExecutionPathsPrimitive(e.getKey()).equals(e.getValue());
		}
		
		
		return consistent;
	}
	

	
	private static <T> boolean compareCollectionsNullOkForFirst(Collection<? extends T> c1, Collection<? extends T> c2) {
		if(c1 == null) {
			return c2.isEmpty();
		} else {
			return c1.equals(c2);
		}
	}

	//This is only used for consistency checks
	void graphConstructionIterationCompleted() {
		if(Globals.useAssertions && LLVMDebuggingFlags.CHECK_FUNCTION_GRAPH_CONSISTENCY_AFTER_EACH_ITERATION) {
			assert allCachesConsistent() : "GRAPH CONSISTENCY ERROR: Function graph inconsistent";
		}
	}
	
	//TODO use me
	private boolean allCachesConsistent() {
		boolean consistent = (allCycles == null || isCycleCacheConsistent());
		consistent &= isNodeCacheConsistent();
		consistent &= isCallNodeCacheConsistent();
		consistent &= isReturnNodeCacheConsistent();
		consistent &= isNonGeneralizedReturnNodeCacheConsistent();
		consistent &= isIntersectionFailureEdgeCacheConsistent();
		consistent &= isIntersectionsCacheConsistent();
		consistent &= isExecutionPathCacheConsistent();
		consistent &= isEntryNodeCacheConsistent();
		consistent &= isNonGeneralizedEntryNodeCacheConsistent();
		consistent &= isReachableCycleCacheConsistent();
		consistent &= allCycles == null ||isCycleCacheConsistent();
		consistent &= nodesToCyclesAndPos == null || isNodeToCyclesAndPosCacheConsistent();
		consistent &= isExecutionPathExistenceCacheConsistent();
		
		return consistent;
				
	}

	private final static EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> doNotUseCallAbstractionEdges =
			(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest, LLVMEdgeInformation label) -> !(label instanceof LLVMCallAbstractionEdge);
			
			
	public String getFunction() {
		return functionName;
	}
	
	public LLVMFunctionGraphSpecificMemoryChangeTracker getMemoryChangeTracker() {
		return memoryChangeTracker;
	}
	
	public boolean isPathAgnostic() {
		return getIntersectionHeuristics().isFunctionPathAgnostic(functionName);
	}


}
