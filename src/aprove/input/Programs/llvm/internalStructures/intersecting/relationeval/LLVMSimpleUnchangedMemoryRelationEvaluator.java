package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMAllocationDeallocationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMUnchangedMemoryRelationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMSimpleUnchangedMemoryRelationEvaluator extends LLVMUnchangedMemoryRelationEvaluator{

	private LLVMFunctionGraph fg;
	private Node<LLVMAbstractState> callNode;
	private LLVMAbstractState callState;
	private LLVMSimpleAllocationDeallocationEvaluator allocationEvaluator;
	private Abortion aborter;
	
	public LLVMSimpleUnchangedMemoryRelationEvaluator(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, LLVMSEPath singleExecutionPath,
			LLVMSimpleAllocationDeallocationEvaluator allocationEvaluator, LLVMImmutableFunctionGraph fg, LLVMModule module, Abortion aborter) {
		super(fg,Collections.singleton(singleExecutionPath),module,aborter);
		this.fg = fg;
		this.callNode = callNode;
		this.callState = callNode.getObject();
		this.aborter = aborter;
		this.allocationEvaluator = allocationEvaluator;
	}
	
	

	
	@Override
	protected UnchangedResult evaluateOnExecutionPathInternal(LLVMSEPath path, LLVMMemoryRange callStateRange) {
		UnchangedResult res = new UnchangedResult();
		
		LLVMAbstractState callState = path.get(0).getObject();
		LLVMAssociationIndex assIndex = callState.getAssociatedAllocationIndex(callStateRange, aborter).x;
		
		if(assIndex == null || assIndex.x == null)
			throw new IllegalStateException("Could not find association for memory range");
		
		LLVMAllocation  callStateAllocation = callState.getAllocations().get(assIndex.x);
		AllocationResult allocationResultForPath = allocationEvaluator.evaluateOnPath(path, callStateAllocation);
		
		if(allocationResultForPath.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE) {
			res.kind = UnchangedResultKind.UNCHANGED_LOST_DURING_MERGE;
			return res;
		} else {
			res.kind = UnchangedResultKind.UNKNOWN;
			return res;
		}
	}

}
