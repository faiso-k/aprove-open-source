package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMMakeRecursiveFunctionGraphUnneededStep extends LLVMIntersectionRelatedStep{

	private final Node<LLVMAbstractState> entryNode;
	
	public LLVMMakeRecursiveFunctionGraphUnneededStep(LLVMSEGraph graph, Node<LLVMAbstractState> entryNode) {
		super(graph);
		this.entryNode = entryNode;
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
	}

	public Node<LLVMAbstractState> getEntryNode() {
		return entryNode;
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		Set<Node<LLVMAbstractState>> generalizationsOfEntryNode = new LinkedHashSet<>();
		
		for(Edge<LLVMEdgeInformation, LLVMAbstractState> edge : graph.getOutEdges(entryNode)) {
			LLVMEdgeInformation label = edge.getObject();
			
			if(label instanceof LLVMGeneralizationInformation) {
				generalizationsOfEntryNode.add(edge.getEndNode());
			}
		}
		
		
		Set<Node<LLVMAbstractState>> unneededNodes = graph.findUnneededNodes(Collections.singleton(entryNode), generalizationsOfEntryNode, null, aborter);
		
		graph.markNodeUnneeded(entryNode);

		unneededNodes.remove(entryNode);
		for (Node<LLVMAbstractState> unneededNode : unneededNodes) {
			if (LLVMDebuggingFlags.REMOVE_TOO_CONCRETE_PARTS_FROM_GRAPH) {
				graph.removeNode(unneededNode);
			} else {
				if (!graph.isNodeUnneeded(unneededNode)) {
					graph.markNodeUnneeded(unneededNode);
				}
			}
		}
		
		return Collections.emptyList();
	}
	
	 

	@Override
	public boolean isObsolete() {
		return !graph.contains(entryNode);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((entryNode == null) ? 0 : entryNode.hashCode());
		return result;
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
		final LLVMMakeRecursiveFunctionGraphUnneededStep other = (LLVMMakeRecursiveFunctionGraphUnneededStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.entryNode != other.entryNode) {
			return false;
		}


		return true;
	}

}
