package aprove.input.Programs.llvm.internalStructures.intersecting.tracker;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMFunctionGraphSpecificMemoryChangeTracker implements LLVMMemoryChangeTracker {

	
	Map<LLVMAbstractState,LLVMAllocation> freedAllocationPerState;
	
	Map<LLVMAbstractState,Set<LLVMMemoryRange>> invalidatedMemoryRangesPerState;
	Map<LLVMAbstractState,LLVMAllocation> invalidatedAllocationPerState;
	
	public LLVMFunctionGraphSpecificMemoryChangeTracker() {
		freedAllocationPerState = new LinkedHashMap<>();
		invalidatedMemoryRangesPerState = new LinkedHashMap<>();
		invalidatedAllocationPerState = new LinkedHashMap<>();
	}
	
	LLVMFunctionGraphSpecificMemoryChangeTracker(LLVMFunctionGraphSpecificMemoryChangeTracker copyMe) {
		freedAllocationPerState = new LinkedHashMap<>(copyMe.freedAllocationPerState);
		invalidatedMemoryRangesPerState = new LinkedHashMap<>(copyMe.invalidatedMemoryRangesPerState);
		invalidatedAllocationPerState = new LinkedHashMap<>(copyMe.invalidatedAllocationPerState);
	}
	
	void removedNodeFromGraph(Node<LLVMAbstractState> node) {
		LLVMAbstractState state = node.getObject();
		freedAllocationPerState.remove(state);
		invalidatedMemoryRangesPerState.remove(state);
		invalidatedAllocationPerState.remove(state);
	}
	
	public LLVMAllocation getAllocationModifiedByStoreEvaluation(Node<LLVMAbstractState> node) {
		LLVMAbstractState state = node.getObject();
		
		if(Globals.useAssertions) {
			assert state.getCurrentInstruction() instanceof LLVMStoreInstruction;
		}
		
		LLVMAllocation resFromMap = invalidatedAllocationPerState.get(state);
		
		if(resFromMap == null) {
			throw new IllegalStateException("Asked for state which we seemingly have not eavaluated?");
		}
		
		return resFromMap;
		
		
	}
	
	public LLVMAllocation getAllocationFreedByFreeEvaluation(Node<LLVMAbstractState> node) {
		LLVMAbstractState state = node.getObject();
		
		if(Globals.useAssertions) {
			assert state.getCurrentInstruction() instanceof LLVMCallInstruction
			&& ((LLVMCallInstruction) state.getCurrentInstruction()).isFreeCall();
		}
		
		LLVMAllocation resFromMap = freedAllocationPerState.get(state);
		
		if(resFromMap == null) {
			throw new IllegalStateException("Asked for state which we seemingly have not eavaluated?");
		}
		
		return resFromMap;
		
		
	}
	
	public Set<LLVMMemoryRange> getMemoryRangesInvalidatedByStore(Node<LLVMAbstractState> node) {
		LLVMAbstractState state = node.getObject();
		
		if(Globals.useAssertions) {
			assert state.getCurrentInstruction() instanceof LLVMStoreInstruction;
		}
		
		Set<LLVMMemoryRange> resFromMap = invalidatedMemoryRangesPerState.get(state);
		
		if(resFromMap == null) {
			throw new IllegalStateException("Asked for state which we seemingly have not eavaluated?");
		}
		
		return resFromMap;
		
		
	}
	
	
	
	@Override
	public void freedAllocationWhenEvaluatingState(LLVMAbstractState state, LLVMAllocation alloc) {
		if(Globals.useAssertions) {
			assert !freedAllocationPerState.containsKey(state) : "Evaluated same state twice?";
			assert state.getCurrentInstruction() instanceof LLVMCallInstruction 
				&& ((LLVMCallInstruction) state.getCurrentInstruction()).isFreeCall();
			assert state.getAllocatedByMalloc().contains(alloc);
				
		}
		
		freedAllocationPerState.put(state, alloc);
		
	}

	@Override
	public void modifiedHeapWhenStoring(LLVMAbstractState state, LLVMAllocation alloc, Set<LLVMMemoryRange> ranges) {
		if(Globals.useAssertions) {
			assert !invalidatedMemoryRangesPerState.containsKey(state) 
						&& !invalidatedAllocationPerState.containsKey(state) : "Evaluated same state twice?";
			assert state.getCurrentInstruction() instanceof LLVMStoreInstruction;
			assert state.getAllocations().contains(alloc);
			assert state.getMemory().keySet().containsAll(ranges);
				
		}
		
		invalidatedMemoryRangesPerState.put(state,ranges);
		invalidatedAllocationPerState.put(state,alloc);
		
	}

}
