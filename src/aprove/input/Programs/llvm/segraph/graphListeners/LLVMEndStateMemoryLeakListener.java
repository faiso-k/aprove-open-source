package aprove.input.Programs.llvm.segraph.graphListeners;

import java.util.Collections;
import java.util.List;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMEndStateMemoryLeakListener extends LLVMSEGraphEventListenerSkeleton{

	public LLVMEndStateMemoryLeakListener(LLVMSEGraph graph) {
		super(graph);
	}
	
	private LLVMParameters getStrategyParameters() {
		return graph.getStrategyParameters();
	}
	
	@Override
	public List<LLVMAbstractGraphConstructionStep> nodeAddedEvent(Node<LLVMAbstractState> node,
			LLVMAbstractGraphConstructionStep currentlyActiveStep)  {
		
		LLVMAbstractState state = node.getObject();
		
		if (state.isEnd()) {
			// MemoryLeakException only thrown when corresponding parameter is
			// set
			if (getStrategyParameters().proveFreeOfMemoryLeaks) {
				//We can't do the check here directly because we can't throw MemoryLeakExceptions here
				return Collections.singletonList(new LLVMCheckForMemoryLeakStep(graph, node));
			}

		}
		return Collections.emptyList();
	}

}
