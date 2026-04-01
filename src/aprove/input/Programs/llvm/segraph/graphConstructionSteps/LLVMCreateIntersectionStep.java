package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphListeners.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

//updated
public class LLVMCreateIntersectionStep extends LLVMIntersectionRelatedStep{

	private final Node<LLVMAbstractState> returnNode;
	private final Node<LLVMAbstractState> callNode;
	
	
	

	//This is "live", i.e., it may be updated between the time this step was created and is actually performed
	private LLVMFunctionGraph functionGraph;
	
	public LLVMCreateIntersectionStep(LLVMSEGraph seGraph, LLVMFunctionGraph functionGraph, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode) {
		super(seGraph);
		this.returnNode = returnNode;
		this.callNode = callNode;
		
		this.functionGraph = functionGraph;
		
		if(Globals.useAssertions) {
			assert !isObsolete(): "Step was obsolete immediately after its creation!";
		}
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		
		//String function = returnNode.getObject().getCurrentFunction();
		Node<LLVMAbstractState> callAbstraction = functionGraph.getCallAbstraction(callNode);
		Node<LLVMAbstractState> entryNode = functionGraph.getMostGeneralEntryNode(callAbstraction);
		
		LLVMIntersectionResult previousIntersection = null;
		
		
				
		
		Set<LLVMSEPath> executionPaths = null;
		
		
		
		Set<LLVMSEPath> relevantCycles = null;
				
				
		if(functionGraph.isPathAgnostic()) {
			previousIntersection = null;
		} else {
			previousIntersection = functionGraph.getMostRecentIntersectionRespectingPresentPathsAndCycles(callNode, returnNode);
			executionPaths = functionGraph.getExecutionPathsViaMostGeneralEntryState(callNode, returnNode);
			relevantCycles = functionGraph.getAllCyclesReachableFromExecutionPaths(executionPaths);
		}
		
		try {
			LLVMIntersector intersector = getStrategyParameters().SMTsolver.stateFactory.createIntersector();
			
			

			LLVMIntersectionResult intersectionResult = intersector.intersect(graph, entryNode, callNode, returnNode, previousIntersection,new LLVMImmutableFunctionGraph(functionGraph), aborter);
			Node<LLVMAbstractState> intersectedNode = intersectionResult.getIntersectedNode();
			//LLVMIntersectionResult intersectionResult = new LLVMIntersectionResult(intersector, intersectedNode);
			
			graph.addEdge(callNode, intersectedNode,
					new LLVMMethodSkipEdge(intersectionResult));
			
			if(intersectionResult.intersectionYieldedResultIdenticalToPreviousIntersection()) {
				//The newly created intersection was identical to the existing one
				
				graph.addEdge(intersectedNode,previousIntersection.getIntersectedNode(), new LLVMIntersectionInstantiationInformation(intersectedNode.getObject()));
				return Collections.emptyList();
			} else {
				// The existing intersection is now obsolete
				ArrayList<LLVMAbstractGraphConstructionStep> resultSteps = new ArrayList<>();
				if (previousIntersection != null) {
					//TODO: handle more obsolete intersections here?
					resultSteps
							.add(new LLVMHandleObsoleteIntersectionStep(graph, previousIntersection.getIntersectedNode()));
				}
				//The intersected node is at a return instruction and can be evaluated as normal
				resultSteps.add(new LLVMStandardStep(graph,intersectedNode));
				return resultSteps;
			}


		} catch (IntersectionFailException e) {
            /*
             * The intersection failed. We make a debug edge to show it.
             * The end of the edge is a clone of the return node which we failed to intersect with (just to see it
             * nicely in the graph).
             */
            Node<LLVMAbstractState> returnNodeCloneNode = new Node<>(returnNode.getObject());
            graph.addEdge(callNode, returnNodeCloneNode, new LLVMFunctionSkipFailureEdge(callNode, returnNode, executionPaths, relevantCycles));
            graph.markNodeUnneeded(returnNodeCloneNode);
            return Collections.emptyList();
        }
	}
	


	@Override
	public boolean isObsolete() {
		//return false; //TODO
		//String function = returnNode.getObject().getCurrentFunction();
		return !graph.contains(returnNode) || 
				!graph.contains(callNode) || 
				!functionGraph.getNonGeneralizedReturnNodes().contains(returnNode) ||
				!LLVMNewIntersectionNeededListener.needToCreateNewIntersection(functionGraph, callNode, returnNode);
						
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((callNode == null) ? 0 : callNode.hashCode());
		result = prime * result + ((functionGraph == null) ? 0 : functionGraph.hashCode());
		result = prime * result + ((returnNode == null) ? 0 : returnNode.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LLVMCreateIntersectionStep other = (LLVMCreateIntersectionStep) obj;
		return callNode == other.callNode && returnNode == other.returnNode && functionGraph == other.functionGraph;
	}



}
