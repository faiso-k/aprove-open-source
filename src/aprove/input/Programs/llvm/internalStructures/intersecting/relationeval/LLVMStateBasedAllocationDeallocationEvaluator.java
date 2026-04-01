package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
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
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class LLVMStateBasedAllocationDeallocationEvaluator extends LLVMAllocationDeallocationEvaluator{

	private LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator;
	private LLVMAbstractState returnState;
	
	public LLVMStateBasedAllocationDeallocationEvaluator(
			LLVMImmutableFunctionGraph fg,
			Set<LLVMSEPath> executionPaths,
			LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator,
			LLVMModule module) {
		super(fg, executionPaths, module);
		this.renamingEvaluator = renamingEvaluator;
		
		LLVMSEPath executionPath = executionPaths.iterator().next();
		returnState = executionPath.get(executionPath.size()-1).getObject();
	}

	public static LLVMAbstractState initializeMapForEntryState(LLVMAbstractState callAbstraction) {
		Map<Integer,Boolean> initialMap = new LinkedHashMap<>();
		for(int allocationIndex = 0; allocationIndex < callAbstraction.getAllocations().size(); allocationIndex++) {
			initialMap.put(allocationIndex, false);
		}
		return callAbstraction.setAllocationChangedSinceEntryState(ImmutableCreator.create(initialMap));
	}

	@Override
	public Pair<Boolean, Boolean> notDeallocated(LLVMAllocation callStateAllocation) {
		throw new UnsupportedOperationException();
	}

	
	protected Pair<LLVMAllocation,Integer> getReturnStateAllocationForCallStateAllocation(LLVMAllocation callStateAllocation) {
		Set<? extends LLVMSimpleTerm> lowerBoundRenamings = null;
		Set<? extends LLVMSimpleTerm> upperBoundRenamings = null;
		
		
		
		if(callStateAllocation.x instanceof LLVMSymbolicVariable) {
			lowerBoundRenamings = renamingEvaluator.getReturnStateVariablesForCallStateVariable((LLVMSymbolicVariable) callStateAllocation.x);
		} else if(callStateAllocation.x instanceof LLVMConstant){
			lowerBoundRenamings = Collections.singleton(callStateAllocation.x);
		}
		if(callStateAllocation.y instanceof LLVMSymbolicVariable) {
			upperBoundRenamings = renamingEvaluator.getReturnStateVariablesForCallStateVariable((LLVMSymbolicVariable) callStateAllocation.y);
		} else if(callStateAllocation.y instanceof LLVMConstant){
			upperBoundRenamings = Collections.singleton(callStateAllocation.y);
		}
		
		for(int returnStateAllocationIndex = 0; returnStateAllocationIndex < returnState.getAllocations().size(); returnStateAllocationIndex++) {
			LLVMAllocation curReturnStateAlloc = returnState.getAllocations().get(returnStateAllocationIndex);
			for(LLVMSimpleTerm lower : lowerBoundRenamings) {
				for(LLVMSimpleTerm upper : upperBoundRenamings) {
					if(curReturnStateAlloc.x.equals(lower) && curReturnStateAlloc.y.equals(upper)) {
						return new Pair<>(curReturnStateAlloc,returnStateAllocationIndex);
					}
						
				}
			}
		}
		
		
		return null;
	}
	
	@Override
	protected AllocationResult evaluateOnExecutionPathInternal(LLVMSEPath executionPath,
			LLVMAllocation callStateAllocation) {
		
		LLVMAbstractState callState = executionPath.get(0).getObject();
		if(Globals.useAssertions) {
			assert callState.getAllocations().contains(callStateAllocation);
		}
		
		AllocationResult res = new AllocationResult();
		res.kind = AllocationResultKind.UNKNOWN;
		
		Node<LLVMAbstractState> callNode = executionPath.get(0);
		Node<LLVMAbstractState> callAbstraction = fg.getCallAbstraction(callNode);
		List<Node<LLVMAbstractState>> part2 = fg.getPathToMostGeneralEntryNode(callAbstraction);
		List<Node<LLVMAbstractState>> prefix = new ArrayList<>();
		prefix.add(callNode);
		prefix.addAll(part2);
		
		LLVMSEPath executionPathsSharedPrefix = new LLVMSEPath(prefix, null);
		
		if(allocationLostDuringGeneralizationOnExecutionPathPrefix(executionPathsSharedPrefix,callStateAllocation)) {
			res.kind = AllocationResultKind.NOT_FREED_LOST_DURING_MERGE;
		} else {
			Pair<LLVMAllocation,Integer> returnStateAllocation  = getReturnStateAllocationForCallStateAllocation(callStateAllocation);
			if(returnStateAllocation != null) {
				Boolean changeFlag = returnState.getAllocationChangedSinceEntryStateMap().get(returnStateAllocation.y);
				if(changeFlag != null) {
					res.kind = AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION;
					res.becameAllocationInLastStateOfPath = returnStateAllocation.x;
					
					if(changeFlag) {
						//mark that there may have been a modification
						res.addIndexWherePossiblyStoredToAllocation(0);
					}
				}
			}
			
			
		}
		
		return res;
		
	}
}
