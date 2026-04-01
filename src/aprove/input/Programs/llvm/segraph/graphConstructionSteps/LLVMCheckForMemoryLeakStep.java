package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.List;
import java.util.logging.Level;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMCheckForMemoryLeakStep extends LLVMAbstractGraphConstructionStep {

	final Node<LLVMAbstractState> endNode;
	
	public LLVMCheckForMemoryLeakStep(LLVMSEGraph graph, Node<LLVMAbstractState> endNode) {
		super(graph);
		this.endNode = endNode;
		
		if(Globals.useAssertions) {
			assert endNode.getObject().isEnd() && getStrategyParameters().proveFreeOfMemoryLeaks;
			assert !isObsolete();
		}
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		if (!endNode.getObject().getAllocatedByMallocIndices().isEmpty()) {
			LLVMWitness witness = LLVMNonterminationProcessor.computeWitness(graph, null, endNode, null,
					new Z3ExtSolverFactory(), aborter);
			if (witness != null) {
				// The state is reachable
				throw new MemoryLeakException("The program contains a memory leak!");
			} else {
				// The state is possibly unreachable (i.e. using
				// SMT-Solving no witness could be found)
				LLVMProblem.logger.log(Level.FINE, "Node " + endNode.getNodeNumber()
						+ " contains probably a memory leak (no witness could be found).\n");
			}
		}
		
		return Collections.emptyList();
	}

	@Override
	public boolean isObsolete() {
		return !graph.contains(endNode);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((endNode == null) ? 0 : endNode.hashCode());
		return result;
	}


	
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (this.getClass() != obj.getClass()) {
			return false;
		}
		final LLVMCheckForMemoryLeakStep other = (LLVMCheckForMemoryLeakStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.endNode != other.endNode) {
			return false;
		}

		return true;
	}

}
