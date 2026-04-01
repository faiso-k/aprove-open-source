package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMHandleCallAbstractionStep extends LLVMIntersectionRelatedStep{

	private final Node<LLVMAbstractState> callNode;

	private final Node<LLVMAbstractState> callAbstractionNode;
	private final LLVMAbstractState callAbstraction;
	
	public LLVMHandleCallAbstractionStep(LLVMSEGraph graph, Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> callAbstractionNode) {
		super(graph);
		this.callNode = callNode;
		this.callAbstractionNode = callAbstractionNode;
		this.callAbstraction = callAbstractionNode.getObject();
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
	}
	

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		if(Globals.useAssertions) {
			assert graph.getOut(callAbstractionNode).isEmpty() : 
				"GRAPH CONSISTENCY ERROR: Node already had successor when we wanted to evaluate it furhter";
		}
		

		LLVMFunctionGraph fg = getFunctionGraphForFunction(callAbstraction.getCurrentFunction());
		Pair<LLVMMergeResult, Node<LLVMAbstractState>> entryStateMergePair = getIntersectionHeuristics()
				.searchGeneralizationOrMergeCallAbstraction(callAbstractionNode, callNode,graph,fg);
		
		if(entryStateMergePair == null) {
			//no merging necessary/no existing suitable more general entry node found 
			return createFreshGraph(callAbstractionNode);
		} else  {
			return handleExistingEntryNode(entryStateMergePair.x,entryStateMergePair.y, aborter);
		}
	}

	

	
	private List<LLVMAbstractGraphConstructionStep> handleExistingEntryNode(LLVMMergeResult entryStateMergeRes,
			Node<LLVMAbstractState> existingEntryNode, Abortion aborter)
			throws MemoryLeakException, UndefinedBehaviorException {
		
		//TODO the current code can deal with the case that the existing node was saved earlier, 
		//but is not in the graph any more. do we still need this?
		if (graph.contains(existingEntryNode) && !graph.isNodeUnneeded(existingEntryNode)) {
			if (entryStateMergeRes.isInstance()) {
				return handleNewCallStateForExistingGraph(existingEntryNode, entryStateMergeRes);
			} else {
				return createNewGraphReplacingExistingOne(existingEntryNode, entryStateMergeRes, aborter);
			}
		} else {
			if (entryStateMergeRes.isInstance()) {
				Node<LLVMAbstractState> freshNodeForExistingEntryState = new Node<>(
						entryStateMergeRes.getGeneralizedState());
				connectAsInstance(freshNodeForExistingEntryState, entryStateMergeRes);
				return createFreshGraph(freshNodeForExistingEntryState);
			} else {
				Node<LLVMAbstractState> generalizedNode = connectAsGeneralization(existingEntryNode, entryStateMergeRes,
						aborter);
				return createFreshGraph(generalizedNode);
			}
		}

	}

	private List<LLVMAbstractGraphConstructionStep> handleNewCallStateForExistingGraph(Node<LLVMAbstractState> existingEntryNode,
			LLVMMergeResult entryStateMergeRes) {
		connectAsInstance(existingEntryNode, entryStateMergeRes);
		//The graph listeners will make sure that Steps for creating the necessary intersections are added to the queue when being notified about the new edge
		return Collections.emptyList();
	}

	
	

	private List<LLVMAbstractGraphConstructionStep> createNewGraphReplacingExistingOne(Node<LLVMAbstractState> existingEntryNode,
			LLVMMergeResult entryStateMergeRes, Abortion aborter) {
		Node<LLVMAbstractState> newEntryNode = connectAsGeneralization(existingEntryNode, entryStateMergeRes, aborter);
		    
		
		List<LLVMAbstractGraphConstructionStep> stepsToDo = new LinkedList<>();
		//stepsToDo.add(new LLVMMakeRecursiveFunctionGraphUnneededStep(graph, existingEntryNode));
		graph.markNodeUnneeded(existingEntryNode);
		
		stepsToDo.addAll(Collections.singletonList(new LLVMStandardStep(graph,newEntryNode)));
		
		String functionName = newEntryNode.getObject().getCurrentFunction();
		graph.setEntryNodeForFunction(functionName, newEntryNode);
		
		return stepsToDo;
	}
	
	private void connectAsInstance(Node<LLVMAbstractState> moreGeneralNode, LLVMMergeResult entryStateMergeRes) {
		final Set<LLVMRelation> changes = callAbstraction.getInvariants();
		final Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap = LLVMSEGraph.getRefCorrespondenceMap(callAbstraction,
				moreGeneralNode.getObject(), entryStateMergeRes.getAllocationBijection());
		graph.addEdge(callAbstractionNode, moreGeneralNode, new LLVMInstantiationInformation(changes, refMap));
	}

	private Node<LLVMAbstractState> connectAsGeneralization(Node<LLVMAbstractState> existingEntryNode,
			LLVMMergeResult entryStateMergeRes, Abortion aborter) {
		LLVMSymbolicEvaluationResult genRes = entryStateMergeRes.getGeneralizedState()
				.flagAbstractRecursiveFunctionStart().postProcessAfterGeneralization(false, aborter);
		LLVMAbstractState generalizedState = genRes.x;
		
		String function = generalizedState.getCurrentFunction();
		if(getIntersectionHeuristics().trackVariableRenamingsInStateForFunction(function)) {
			generalizedState = LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.initEntryStateVarMapForEntryState(generalizedState);
		}
		if(getIntersectionHeuristics().trackAllocationModificationInStateForFunction(function)) {
			generalizedState = LLVMStateBasedAllocationDeallocationEvaluator.initializeMapForEntryState(generalizedState);
		}
		
		Node<LLVMAbstractState> generalizedNode = new Node<>(generalizedState);

		final Map<LLVMSimpleTerm, LLVMSimpleTerm> newRefMap = LLVMSEGraph.getRefCorrespondenceMap(callAbstraction,
				genRes.x, entryStateMergeRes.getAllocationBijection(false));
		final Map<LLVMSimpleTerm, LLVMSimpleTerm> partnerRefMap = LLVMSEGraph.getRefCorrespondenceMap(
				existingEntryNode.getObject(), genRes.x, entryStateMergeRes.getAllocationBijection(true));
		graph.addEdge(callAbstractionNode, generalizedNode,
				new LLVMGeneralizationInformation(existingEntryNode, genRes.y, newRefMap));
		if (graph.contains(existingEntryNode)) {
			graph.addEdge(existingEntryNode, generalizedNode,
					new LLVMGeneralizationInformation(callAbstractionNode, genRes.y, partnerRefMap));
		}
		
		return generalizedNode;
	}
	
	
	private List<LLVMAbstractGraphConstructionStep> createFreshGraph(Node<LLVMAbstractState> entryNode) {
		return Collections.singletonList(new LLVMStandardStep(graph, entryNode));
	}
	

	
	

	
	@Override
	public boolean isObsolete() {
		return !graph.contains(callAbstractionNode);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((callAbstractionNode == null) ? 0 : callAbstractionNode.hashCode());
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
        final LLVMHandleCallAbstractionStep other = (LLVMHandleCallAbstractionStep) obj;
        if (this.graph != other.graph) {
            return false;
        }
        
        if (this.callAbstraction != other.callAbstraction) {
            return false;
        }
        
        if (this.callAbstractionNode != other.callAbstractionNode) {
            return false;
        }
        
        
        
        return true;
    }


	public Node<LLVMAbstractState> getCallAbstractionNode() {
		return callAbstractionNode;
	}

}
