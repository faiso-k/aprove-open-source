package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;


public class LLVMEntryNodeOfRecursiveFunctionRemovedOrUnneededListener extends LLVMSEGraphEventListenerSkeleton {

	public LLVMEntryNodeOfRecursiveFunctionRemovedOrUnneededListener(LLVMSEGraph graph) {
		super(graph);
	}


	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeRemovedOrUnneeded(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep, boolean removed) {
		if(currentlyActiveStep instanceof LLVMMakeRecursiveFunctionGraphUnneededStep) {
			LLVMMakeRecursiveFunctionGraphUnneededStep step = (LLVMMakeRecursiveFunctionGraphUnneededStep) currentlyActiveStep;
			if(step.getEntryNode() == node)
				return Collections.emptyList();  //Already been taken care of
		}
		
		if(getIntersectionHeuristics().isCallAbstractionOrEntryState(node.getObject()) && !removed) {
			return Collections.singletonList(new LLVMMakeRecursiveFunctionGraphUnneededStep(graph,node));
		}
		
		return Collections.emptyList();
	}

	



}
