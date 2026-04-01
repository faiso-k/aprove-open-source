package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.Collections;
import java.util.List;

import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;


//If a return node is removed or made unneeded in the  the SEGraph, we create a step such that intersections with it
//are marked as unneeded or removed from the SEGraph, too.
public class LLVMReturnNodeRemovedOrUnneededListener extends LLVMSEGraphEventListenerSkeleton {

	public LLVMReturnNodeRemovedOrUnneededListener(LLVMSEGraph graph) {
		super(graph);
	}



	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeRemovedOrUnneeded(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed) {
		if(getIntersectionHeuristics().isReturnState(node.getObject())) {
			String function = node.getObject().getCurrentFunction();
			LLVMFunctionGraph fg = graph.getFunctionGraphTracker().getFunctionGraph(function);
			return LLVMHandleReturnStateStep.createRemovalStepsForOldReturnStateIntersections(graph,fg,node);
		}
		return Collections.emptyList();
		
	}



	
	

}
