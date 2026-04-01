package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;


public class LLVMHandleObsoleteIntersectionStep extends LLVMAbstractGraphConstructionStep{

    private final int hashCode;
	
	private final Node<LLVMAbstractState> intersection;
	
	
	public LLVMHandleObsoleteIntersectionStep(LLVMSEGraph graph, Node<LLVMAbstractState> intersection) {
		super(graph);
		this.intersection = intersection;
		
		this.hashCode = this.graph.hashCode();
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		Set<Node<LLVMAbstractState>> unneededNodes = graph.findUnneededNodes(Collections.singleton(intersection), Collections.emptySet(), null, aborter);
		
		
		for(Node<LLVMAbstractState> unneededNode : unneededNodes) {
			if(LLVMDebuggingFlags.REMOVE_TOO_CONCRETE_PARTS_FROM_GRAPH) {
				graph.removeNode(unneededNode);
			} else {
				if(!graph.isNodeUnneeded(unneededNode)) {
					graph.markNodeUnneeded(unneededNode);
				}
			}
		}
		
		return Collections.emptyList();
	}

	@Override
	public boolean isObsolete() {
		return !graph.contains(intersection);
	}

    @Override
    public int hashCode() {
        return hashCode;
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
		final LLVMHandleObsoleteIntersectionStep other = (LLVMHandleObsoleteIntersectionStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.intersection != other.intersection) {
			return false;
		}


		return true;
	}

}
