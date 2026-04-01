package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMHandleReturnStateStep extends LLVMIntersectionRelatedStep {

	private final Node<LLVMAbstractState> returnNode;
	

	private final LLVMAbstractState returnState;
	
	LLVMHandleReturnStateStep(LLVMSEGraph graph, Node<LLVMAbstractState> returnNode) {
		super(graph);
		this.returnNode = returnNode;
		this.returnState = returnNode.getObject();
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
		
	}

	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException,
			UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		//Node<LLVMAbstractState> existingReturnNode = getMatchingReturnNodeDifferentFromNewOne();
		LLVMFunctionGraph fg = getFunctionGraphForFunction(returnState.getCurrentFunction());

		Pair<LLVMMergeResult, Node<LLVMAbstractState>> existingReturnNodeMergePair = getIntersectionHeuristics()
				.searchGeneralizationOrMergeReturnNode(returnNode,graph,fg);
		
		if(existingReturnNodeMergePair != null) {
			return handleExistingReturnNode(existingReturnNodeMergePair.x, existingReturnNodeMergePair.y, aborter);
		} else {
			//The new intersections are created by the corresponding listener on the graph, no need to do that here
			return Collections.emptyList();
		}
	}
	
	public static List<LLVMAbstractGraphConstructionStep> createRemovalStepsForOldReturnStateIntersections(LLVMSEGraph graph, LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode) {
		//Use the "primitive" versions here because this may be called from the listener for removed return nodes
		//thus, the function graph may not have updated itself at this point and it would raise an assertion error due to its inconsistency
		Set<Node<LLVMAbstractState>> callNodes = fg.getCallNodesPrimitive();
		Set<LLVMIntersectionResult> intersectionsWithGivenReturnState = new LinkedHashSet<>();
		for(Node<LLVMAbstractState> callNode : callNodes) {
			intersectionsWithGivenReturnState.addAll(fg.getIntersectionsPrimitive(callNode,returnNode));
		}
		
		
		List<LLVMAbstractGraphConstructionStep> steps = new ArrayList<>(intersectionsWithGivenReturnState.size());
		
		for(LLVMIntersectionResult obsoleteIntersection: intersectionsWithGivenReturnState) {
			steps.add(new LLVMHandleObsoleteIntersectionStep(graph, obsoleteIntersection.getIntersectedNode()));
		}
		
		return steps;
	}
	


	private List<LLVMAbstractGraphConstructionStep> handleExistingReturnNode(LLVMMergeResult mergeResult,
			Node<LLVMAbstractState> existingReturnNode, Abortion aborter)
			throws MemoryLeakException, UndefinedBehaviorException {
		LLVMAbstractState existingReturnState = existingReturnNode.getObject();
		
        
        if(mergeResult.isInstance()) {
        	final Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap =
                    LLVMSEGraph.getRefCorrespondenceMap(
                        returnState,
                        existingReturnState,
                        mergeResult.getAllocationBijection()
                    );
                final Set<LLVMRelation> set = returnState.getInvariants();
                graph.addEdge(
                    returnNode,
                    existingReturnNode,
                    new LLVMInstantiationInformation(set, refMap)
                );
                return Collections.emptyList();
        } else {
        	LLVMSymbolicEvaluationResult genRes =
                    mergeResult.getGeneralizedState().postProcessAfterGeneralization(false, aborter);
                Node<LLVMAbstractState> generalizedNode = new Node<LLVMAbstractState>(genRes.x);
                final Map<LLVMSimpleTerm, LLVMSimpleTerm> newRefMap =
                    LLVMSEGraph.getRefCorrespondenceMap(
                        returnState,
                        genRes.x,
                        mergeResult.getAllocationBijection(false)
                    );
                final Map<LLVMSimpleTerm, LLVMSimpleTerm> partnerRefMap =
                    LLVMSEGraph.getRefCorrespondenceMap(
                        existingReturnState,
                        genRes.x,
                        mergeResult.getAllocationBijection(true)
                    );
                graph.addEdge(
                    returnNode,
                    generalizedNode,
                    new LLVMGeneralizationInformation(existingReturnNode, genRes.y, newRefMap)
                );
                graph.addEdge(
                    existingReturnNode,
                    generalizedNode,
                    new LLVMGeneralizationInformation(returnNode, genRes.y, partnerRefMap)
                );
                LLVMFunctionGraph fg = getFunctionGraphForFunction(returnState.getCurrentFunction());

                //We have generalized an existing return node. we do not need intersections with it any more
                List<LLVMAbstractGraphConstructionStep> removalSteps = new ArrayList<>();
                removalSteps.addAll(createRemovalStepsForOldReturnStateIntersections(graph, fg,existingReturnNode));
                removalSteps.addAll(createRemovalStepsForOldReturnStateIntersections(graph, fg,returnNode));
                return removalSteps;
        }
        
        //The new intersections (if needed) are created by the corresponding listener on the graph, no need to do that here
	}
	
	@Override
	public boolean isObsolete() {
		LLVMFunctionGraph fg = getFunctionGraphForFunction(returnState.getCurrentFunction());
		return !graph.contains(returnNode) || fg.outgoingGeneralizationEdgeCount(returnNode) > 0;
	}
	
	public Node<LLVMAbstractState> getReturnNode() {
		return returnNode;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((returnNode == null) ? 0 : returnNode.hashCode());
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
		final LLVMHandleReturnStateStep other = (LLVMHandleReturnStateStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.returnNode != other.returnNode) {
			return false;
		}


		return true;
	}

}
