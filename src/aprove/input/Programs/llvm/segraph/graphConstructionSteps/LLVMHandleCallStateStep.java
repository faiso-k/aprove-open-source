package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.List;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;


/**
 * Handles call states.
 * Creates the (simplified) call abstraction and puts it in the queue
 */
public class LLVMHandleCallStateStep extends LLVMIntersectionRelatedStep{

	final private Node<LLVMAbstractState> callNode;
	final private LLVMAbstractState callState;
	
	private Node<LLVMAbstractState> callAbstractionNode;
	private LLVMAbstractState callAbstraction;
	
	
	
	LLVMHandleCallStateStep(LLVMSEGraph graph, Node<LLVMAbstractState> newCallNode) {
		super(graph);
		this.callNode = newCallNode;
		this.callState = callNode.getObject();
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		if(Globals.useAssertions) {
			assert graph.contains(callNode);
		}
		if(Globals.useAssertions) {
			assert graph.getOut(callNode).isEmpty() : 
				"GRAPH CONSISTENCY ERROR: Node already had successor when we wanted to evaluate it furhter";
		}
		
        callAbstraction = getIntersectionHeuristics().createSimplifiedCallAbstraction(callState, aborter);
        callAbstractionNode = new Node<LLVMAbstractState>(callAbstraction);

        graph.addEdge(callNode,callAbstractionNode,new LLVMCallAbstractionEdge());
        
        return Collections.singletonList(new LLVMHandleCallAbstractionStep(graph,callNode, callAbstractionNode));
	}
	

	
	


	
	@Override
	public boolean isObsolete() {
		return !graph.contains(callNode);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((callNode == null) ? 0 : callNode.hashCode());
		result = prime * result + ((callAbstractionNode == null) ? 0 : callAbstractionNode.hashCode());
		return result;
	}
	
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (this.getClass() != obj.getClass()) {
			return false;
		}
		final LLVMHandleCallStateStep other = (LLVMHandleCallStateStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.callAbstraction != other.callAbstraction) {
			return false;
		}

		if (this.callAbstractionNode != other.callAbstractionNode) {
			return false;
		}

		if (this.callNode != other.callNode) {
			return false;
		}

		if (this.callState != other.callState) {
			return false;
		}

		return true;
	}



}
