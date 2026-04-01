package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.LLVMAllocationDeallocationEvaluator.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMSimpleAllocationDeallocationEvaluator extends LLVMAllocationDeallocationEvaluator {


	private Node<LLVMAbstractState> callNode;
	private LLVMAbstractState callState;
	private LLVMSEPath executionPathsSharedPrefix;
	
	public LLVMSimpleAllocationDeallocationEvaluator(Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, LLVMSEPath singleExecutionPath, LLVMImmutableFunctionGraph fg, LLVMModule module) {
		super(fg,Collections.singleton(singleExecutionPath), module);
		this.callNode = callNode;
		this.callState = callNode.getObject();
		Node<LLVMAbstractState> callAbstraction = fg.getCallAbstraction(callNode);
		List<Node<LLVMAbstractState>> part2 = fg.getPathToMostGeneralEntryNode(callAbstraction);
		List<Node<LLVMAbstractState>> prefix = new ArrayList<>();
		prefix.add(callNode);
		prefix.addAll(part2);
		
		executionPathsSharedPrefix = new LLVMSEPath(prefix, null);
	}
	

	
	@Override
	protected  AllocationResult evaluateOnExecutionPathInternal(LLVMSEPath executionPath, LLVMAllocation callStateAllocation) {
		if(Globals.useAssertions) {
			assert callState.getAllocations().contains(callStateAllocation);
		}
		
		AllocationResult res = new AllocationResult();
		
		if(allocationLostDuringGeneralizationOnExecutionPathPrefix(executionPathsSharedPrefix,callStateAllocation)) {
			res.kind = AllocationResultKind.NOT_FREED_LOST_DURING_MERGE;
		} else {
			res.kind = AllocationResultKind.UNKNOWN;
		}
		
		return res;
	}



	@Override
	public Pair<Boolean, Boolean> notDeallocated(LLVMAllocation callStateAllocation) {
		throw new UnsupportedOperationException();
	}




	

	
	

}
