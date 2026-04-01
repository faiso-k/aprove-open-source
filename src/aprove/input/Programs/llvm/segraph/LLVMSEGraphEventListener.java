package aprove.input.Programs.llvm.segraph;

import java.util.List;

import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;
/**
 * * Important: None of the methods in this interface must change the graph when
 * being called. If a listener wants to change the graph, it must return a list
 * of corresponding graph construction steps.
 * 
 * All events here are triggered when the event has already taken place
 * 
 * @author Frank Emrich
 *
 */
public interface LLVMSEGraphEventListener {

	/**
	 * Called after a new edge was added to the graph.
	 * If start or end is a new node, then it is guaranteed that addNode has been called beforehand for that nodes
	 * 
	 * @param currentlyActiveStep The graph construction step that was active when this event fired
	 * @return A set of steps that should be added to the queue of steps to perform
	 */
	List<LLVMAbstractGraphConstructionStep> edgeAddedEvent(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end,
			LLVMEdgeInformation label, LLVMAbstractGraphConstructionStep currentlyActiveStep);

	/**
	 * Called after an edge was removed from the graph or its start node or end node became unneeded.
	 * Note that this is does not imply the removal of the nodes from the graph.
	 * 
	 * 
	 * @param currentlyActiveStep The graph construction step that was active when this event fired
	 * @return A set of steps that should be added to the queue of steps to perform
	 */
	List<LLVMAbstractGraphConstructionStep> edgeRemovedOrUnneeded(Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> end, LLVMEdgeInformation label,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed);

	/**
	 * Called after a node was added to the graph 
	 * 
	 * @param currentlyActiveStep The graph construction step that was active when this event fired
	 * @return A set of steps that should be added to the queue of steps to perform
	 */
	List<LLVMAbstractGraphConstructionStep> nodeAddedEvent(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep);

	/**
	 * Called after a node was removed from the graph or marked as unneeded.
	 * edgeRemovedOrUnneeded is called beforehand for all edges starting or ending in the node
	 * 
	 * @param currentlyActiveStep The graph construction step that was active when this event fired
	 * @return A set of steps that should be added to the queue of steps to perform
	 */
	List<LLVMAbstractGraphConstructionStep> nodeRemovedOrUnneeded(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed);

	/**
	 * Called after each iteration of the graph construction loop, i.e., after one 
	 * graph construction step was performed
	 * 
	 * @param currentlyActiveStep The graph construction step that was just performed
	 * @return A set of steps that should be added to the queue of steps to perform
	 */
	List<LLVMAbstractGraphConstructionStep> completedGraphConstructionIterationEvent();

	/**
	 * Called once when the graph construction finishes
	 * 
	 */
	void graphFinishedEvent();

}