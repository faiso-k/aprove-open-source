package aprove.input.Programs.llvm.internalStructures.intersecting.tracker;


import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

//Use for lazy evaluation of intersetion stuff
public class LLVMImmutableFunctionGraph extends LLVMFunctionGraph {

	public LLVMImmutableFunctionGraph(LLVMFunctionGraph toBeCopied) {
		super(toBeCopied);
		
		//use copies of sets when initializing things!
	}

	@Override
	void edgeAdded(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void edgeRemoved(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void nodeAdded(Node<LLVMAbstractState> newNode) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void nodeRemoved(Node<LLVMAbstractState> existingNode) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void callNodeAdded(Node<LLVMAbstractState> callNode) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void callNodeRemoved(Node<LLVMAbstractState> callNode) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void intersectionAdded(LLVMIntersectionResult intersectionRes) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}

	@Override
	void intersectionRemoved(LLVMIntersectionResult intersectionRes) {
		throw new UnsupportedOperationException("Notified immutable function graph about change!");
	}
}
