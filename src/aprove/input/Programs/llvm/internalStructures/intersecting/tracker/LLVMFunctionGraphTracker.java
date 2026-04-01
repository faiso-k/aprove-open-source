package aprove.input.Programs.llvm.internalStructures.intersecting.tracker;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.segraph.graphListeners.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMFunctionGraphTracker extends LLVMSEGraphEventListenerSkeleton {

	private final Map<String,LLVMFunctionGraph> intersectableFunctionsToGraph;
	private final LLVMIntersectionHeuristics heuristics;
	
	public LLVMFunctionGraphTracker(LLVMSEGraph graph, LLVMIntersectionHeuristics heuristics) {
		super(graph);
		this.intersectableFunctionsToGraph = new LinkedHashMap<>();
		this.heuristics = heuristics;
	}

	public LLVMFunctionGraph getFunctionGraph(String functionName) {
		if(heuristics.isIntersectableFunction(functionName)) {
			LLVMFunctionGraph graph = intersectableFunctionsToGraph.get(functionName);
			if(graph == null) {
				throw new IllegalStateException("Asked for function graph before it was created");
			} else {
				return graph;
			}
		} else {
			throw new IllegalArgumentException("Asked for function graph of non-intersectable function!");
		}
	}

	
	private LLVMFunctionGraph createOrGetFunctionGraph(String intersectableFunction) {
		return intersectableFunctionsToGraph.computeIfAbsent(intersectableFunction, f -> new LLVMFunctionGraph(f,graph,heuristics));
	}

	//there may be summarizable functions for which this does not return a graph,
	//if none has been created so far
	public Set<LLVMFunctionGraph> getAllFunctionGraphs() {
		return new LinkedHashSet<>(intersectableFunctionsToGraph.values());
	}
	
	
	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeAddedEvent(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep) {
		LLVMAbstractState state = node.getObject();
		if(getIntersectionHeuristics().bottomMostFunctionIntersectable(state)) {
			String bottomMostFunction = state.getBottommostFunctionInStack();
			LLVMFunctionGraph fg = createOrGetFunctionGraph(bottomMostFunction);
			fg.nodeAdded(node);
			
		}
		
		if(getIntersectionHeuristics().isCallState(state)) {
			String topMostFunction = state.getCurrentFunction();
			LLVMFunctionGraph fg = createOrGetFunctionGraph(topMostFunction);
			fg.callNodeAdded(node);
		}
		
		
		
		return Collections.emptyList();
	}
	


	
	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeRemovedOrUnneeded(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed) {
		if(removed) {
			LLVMAbstractState state = node.getObject();
			if (getIntersectionHeuristics().bottomMostFunctionIntersectable(state)) {
				String bottomMostFunction = state.getBottommostFunctionInStack();
				LLVMFunctionGraph fg = createOrGetFunctionGraph(bottomMostFunction);
				fg.nodeRemoved(node);

			}

			if (getIntersectionHeuristics().isCallState(state)) {
				String topMostFunction = state.getCurrentFunction();
				LLVMFunctionGraph fg = createOrGetFunctionGraph(topMostFunction);
				fg.callNodeRemoved(node);
			}

		}
		return Collections.emptyList();
	}
	
	@Override
	public List<LLVMAbstractGraphConstructionStep> edgeAddedEvent(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label,
			LLVMAbstractGraphConstructionStep currentlyActiveStep) {
		LLVMAbstractState startState = start.getObject();
		LLVMAbstractState endState = end.getObject();
		
		LLVMFunctionGraph fgStart = null;
		LLVMFunctionGraph fgEnd = null;
		
		if(getIntersectionHeuristics().bottomMostFunctionIntersectable(startState)) { 
			String bottomMostFunction = startState.getBottommostFunctionInStack();
			 fgStart = createOrGetFunctionGraph(bottomMostFunction);
			
		} 
		if(getIntersectionHeuristics().bottomMostFunctionIntersectable(endState)) {
			//using else if here to prevent calling the same function graph twice for the same edge
			String bottomMostFunction = endState.getBottommostFunctionInStack();
			fgEnd = createOrGetFunctionGraph(bottomMostFunction);
		}
		
		if(fgStart != null) {
			fgStart.edgeAdded(start, end, label);
		} 
		if(fgEnd != null && fgEnd != fgStart) {
			//avoid telling the same graph twice
			fgEnd.edgeAdded(start, end, label);
		}
		
		
		
		if(label instanceof LLVMMethodSkipEdge) {
			LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) label;
			String topmostFunction = endState.getCurrentFunction();
			LLVMFunctionGraph fg = createOrGetFunctionGraph(topmostFunction);
			fg.intersectionAdded(skipEdge.getIntersectionResult());
		}
		
		
		return Collections.emptyList();
		
	}

	
	@Override
	public List<LLVMAbstractGraphConstructionStep> edgeRemovedOrUnneeded(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed) {
		if(removed) {
			LLVMAbstractState startState = start.getObject();
			LLVMAbstractState endState = end.getObject();

			if (getIntersectionHeuristics().bottomMostFunctionIntersectable(startState)) {
				String bottomMostFunction = startState.getBottommostFunctionInStack();
				LLVMFunctionGraph fg = createOrGetFunctionGraph(bottomMostFunction);
				fg.edgeRemoved(start, end, label);

			} else if (getIntersectionHeuristics().bottomMostFunctionIntersectable(endState)) {
				// using else if here to prevent calling the same function graph
				// twice for the same edge
				String bottomMostFunction = endState.getBottommostFunctionInStack();
				LLVMFunctionGraph fg = createOrGetFunctionGraph(bottomMostFunction);
				fg.edgeRemoved(start, end, label);
			}

			if (label instanceof LLVMMethodSkipEdge) {
				LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) label;
				String topmostFunction = endState.getCurrentFunction();
				LLVMFunctionGraph fg = createOrGetFunctionGraph(topmostFunction);
				fg.intersectionRemoved(skipEdge.getIntersectionResult());
			}
		
		}
		return Collections.emptyList();
	
	}

	public List<LLVMAbstractGraphConstructionStep> completedGraphConstructionIterationEvent() {
		for(LLVMFunctionGraph fg : getAllFunctionGraphs()) {
			fg.graphConstructionIterationCompleted();
		}
		return Collections.emptyList();
	}
	

}
