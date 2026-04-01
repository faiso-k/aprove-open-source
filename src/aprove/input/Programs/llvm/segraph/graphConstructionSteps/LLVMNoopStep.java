package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.List;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.strategies.Abortions.*;

public class LLVMNoopStep extends LLVMAbstractGraphConstructionStep {

	public LLVMNoopStep(LLVMSEGraph graph) {
		super(graph);
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug)
			throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException,
			MemoryLeakException {
		
		//Do nothing, return that nothing else needs to be done
		return Collections.emptyList();
	}

	@Override
	public boolean isObsolete() {
		return true;
	}

}
