package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

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

public class LLVMStateBasedUnchangedMemoryRelationEvaluator extends LLVMUnchangedMemoryRelationEvaluator {

	private final LLVMAllocationDeallocationEvaluator allocationEvaluator;
	
	public LLVMStateBasedUnchangedMemoryRelationEvaluator(LLVMImmutableFunctionGraph fg, Set<LLVMSEPath> executionPaths, LLVMAllocationDeallocationEvaluator allocationEvaluator,
			LLVMModule module, Abortion aborter) {
		super(fg, executionPaths, module, aborter);
		this.allocationEvaluator = allocationEvaluator;
	}

	@Override
	protected UnchangedResult evaluateOnExecutionPathInternal(LLVMSEPath path, LLVMMemoryRange callStateRange) {
		UnchangedResult result = new UnchangedResult();
		result.kind = UnchangedResultKind.UNKNOWN;
		
		LLVMAbstractState callState = path.get(0).getObject();
		LLVMAssociationIndex assIndex = callState.getAssociatedAllocationIndex(callStateRange, aborter).x;
		
		if(assIndex == null || assIndex.x == null)
			throw new IllegalStateException("Could not find association for memory range");
		
		LLVMAllocation  callStateAllocation = callState.getAllocations().get(assIndex.x);
		AllocationResult allocationResultForPath = allocationEvaluator.evaluateOnPath(path, callStateAllocation);
		
		if(allocationResultForPath.kind == AllocationResultKind.NOT_FREED_LOST_DURING_MERGE
				&&  allocationResultForPath.getIndicesOnPathWhereAllocationWasPossiblyStoredTo().isEmpty()) {
			result.kind = UnchangedResultKind.UNCHANGED_LOST_DURING_MERGE;
		}
		
		if(allocationResultForPath.kind == AllocationResultKind.NOT_FREED_TURNED_INTO_LAST_STATE_ALLOCATION
				&&  allocationResultForPath.getIndicesOnPathWhereAllocationWasPossiblyStoredTo().isEmpty()) {
			result.kind = UnchangedResultKind.UNCHANGED_LOST_TRACK_OF_NAME; 
		}
		

			
		return result;
	}

}
