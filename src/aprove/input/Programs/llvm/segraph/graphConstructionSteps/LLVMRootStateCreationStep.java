package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.List;

import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMRootStateCreationStep extends LLVMAbstractGraphConstructionStep {

	private LLVMQuery query;
	
	public LLVMRootStateCreationStep(LLVMSEGraph graph, LLVMQuery query) {
		super(graph);
		this.query = query;
	}
	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) {
		LLVMAbstractState rootState = getStrategyParameters().SMTsolver.stateFactory.createBeginState(query, getModule(), getStrategyParameters(), aborter);
		rootState = rootState.retainLiveVariables(graph.getLiveVariableAnalysis().getLiveVariables(graph.getModule()).get(rootState.getProgramPosition()), false);
		if(rootState instanceof LLVMHeuristicState) {
			LLVMHeuristicState heuristicRoot = (LLVMHeuristicState) rootState;
			heuristicRoot = heuristicRoot.retainReachableAllocationsAndHeapInfo(aborter);
			rootState = heuristicRoot.restrictToUsedReferences(null, aborter);
		}
		String rootFunction = rootState.getCurrentFunction();
		if(getIntersectionHeuristics().trackVariableRenamingsInStateForFunction(rootFunction)) {
			rootState = LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.initEntryStateVarMapForEntryState(rootState);
		}
		if(getIntersectionHeuristics().trackAllocationModificationInStateForFunction(rootFunction)) {
			rootState = LLVMStateBasedAllocationDeallocationEvaluator.initializeMapForEntryState(rootState);
		}
		
		Node<LLVMAbstractState> rootNode = new Node<LLVMAbstractState>(rootState);
		
		graph.addNode(rootNode);
		graph.setRoot(rootNode);
		
		String function = rootNode.getObject().getCurrentFunction();
		
		return Collections.singletonList(new LLVMStandardStep(graph,rootNode));
	}
	@Override
	public boolean isObsolete() {
		return false;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((query == null) ? 0 : query.hashCode());
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
		final LLVMRootStateCreationStep other = (LLVMRootStateCreationStep) obj;
		if (this.graph != other.graph) {
			return false;
		}
		
		if (this.query == null) {
            if (other.query != null) {
                return false;
            }
        } else if (!this.query.equals(other.query)) {
            return false;
        }



		return true;
	}

}
