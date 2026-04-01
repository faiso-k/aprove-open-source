package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.Collections;
import java.util.List;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Sekeleton providing default implementations that do nothing
 */
public abstract class LLVMSEGraphEventListenerSkeleton implements LLVMSEGraphEventListener {

	public LLVMSEGraphEventListenerSkeleton(LLVMSEGraph graph) {
		this.graph = graph;
	}
	
	protected final LLVMSEGraph graph;
	
	protected LLVMIntersectionHeuristics getIntersectionHeuristics() {
		return graph.getIntersectionHeuristics();
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> edgeAddedEvent(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end,
			LLVMEdgeInformation label, LLVMAbstractGraphConstructionStep currentlyActiveStep) {
		return Collections.emptyList(); 
	}


	@Override
	public List<LLVMAbstractGraphConstructionStep> edgeRemovedOrUnneeded(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed)  {
		return Collections.emptyList();
	}


	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeAddedEvent(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep) {
		return Collections.emptyList();
	}


	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeRemovedOrUnneeded(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed) {
		return Collections.emptyList();
	}


	@Override
	public List<LLVMAbstractGraphConstructionStep> completedGraphConstructionIterationEvent() {
		return Collections.emptyList();
	}


	@Override
	public void graphFinishedEvent() {
		
	}

}
