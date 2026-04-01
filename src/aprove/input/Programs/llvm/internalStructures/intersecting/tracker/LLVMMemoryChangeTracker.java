package aprove.input.Programs.llvm.internalStructures.intersecting.tracker;

import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.states.*;

public interface LLVMMemoryChangeTracker {

	void freedAllocationWhenEvaluatingState(LLVMAbstractState state, LLVMAllocation alloc);
	
	void modifiedHeapWhenStoring(LLVMAbstractState state, LLVMAllocation alloc, Set<LLVMMemoryRange> ranges);
	
}
