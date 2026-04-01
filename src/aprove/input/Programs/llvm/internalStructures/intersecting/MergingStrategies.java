package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class MergingStrategies {

enum EntryStateMergingStrategy {
	//always merge entry states such that there will always be only one (which is not generalized)
	ENFORCE_SINGLE_ENTRY_STATE_PER_FUNCTION {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> entryNode,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			if(Globals.useAssertions) {
				assert existingCallNodeEntryNodeTuples
				.stream()
				.map(p -> p.y)
				.collect(Collectors.toCollection(LinkedHashSet::new))
				.size() <= 1 : "GRAPH CONSISTENCY ERROR: Had more than one existing entry node, although we enforce that there should be at most one";
			}
			return existingCallNodeEntryNodeTuples
					.stream()
					.map(p -> p.y)
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},

	//merge entry states if they both follow (in the graph, using call abstraction and gen. edges) from call abstractions with the same stack
	MERGE_CALL_STACK_BASED_MUST_HAVE_SAME_NUMBER_OF_ALLOCATIONS{
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> callAbstraction,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			LLVMAbstractState callAbstractionState = callAbstraction.getObject();
			LLVMAbstractState callState = callNode.getObject();
			return existingCallNodeEntryNodeTuples
					.stream()
					.filter(p -> p.x != null && LLVMIntersectionHeuristics.haveMatchingStacks(p.x.getObject(),callState,true) 
							&& p.y.getObject().getAllocations().size() == callAbstractionState.getAllocations().size())
					.map(p -> p.y)
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},
	MERGE_CALL_STACK_BASED_DO_NOT_CONSIDER_NUMBER_OF_ALLOCATIONS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> callAbstraction,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			LLVMAbstractState callState = callNode.getObject();
			return existingCallNodeEntryNodeTuples
					.stream()
					.filter(p -> p.x != null && LLVMIntersectionHeuristics.haveMatchingStacks(p.x.getObject(),callState,false))
					.map(p -> p.y)
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},

	//merge if one has a path to the other (respecting all edges)
	MERGE_REACHABILITY_BASED_MUST_HAVE_SAME_NUMBER_OF_ALLOCATIONS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> callAbstraction,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> seGraph = fg.getGraph();
			LLVMAbstractState callAbstractionState = callAbstraction.getObject();
			return existingCallNodeEntryNodeTuples
					.stream()
					.filter(p -> seGraph.hasPath(p.y, callAbstraction) 
							&& p.y.getObject().getAllocations().size() == callAbstractionState.getAllocations().size())
					.map(p -> p.y)
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},
	MERGE_REACHABILITY_DO_NOT_CONSIDER_NUMBER_OF_ALLOCATIONS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> callAbstraction,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> seGraph = fg.getGraph();
			return existingCallNodeEntryNodeTuples
					.stream()
					.filter(p -> seGraph.hasPath(p.y, callAbstraction))
					.map(p -> p.y)
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},

	NEVER_MERGE {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
				Node<LLVMAbstractState> callAbstraction,
				Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples) {
			return Collections.emptySet();
		}
	};
	
	/**
	 * 
	 * @param fg
	 * @param callNodeEntryNodeTuples set of pairs (x,y) where y is an entry node without an outgoing gen. edge, and x is a call node that has a path to y consisting
	 * of at most one call abstraction edge and arbitratily many gen. edges. x may be null, y not
	 * There must be no pair in the set such that x == callNode or y == callAbstraction.
	 * Note that the same y may appear in several pairs
	 * @return A set of nodes which we must merge reference with (more precisely, we merge with the best fit, as usually)
	 */
	abstract Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> callNode,
			Node<LLVMAbstractState> callAbstraction,
			Set<Pair<Node<LLVMAbstractState>, Node<LLVMAbstractState>>> existingCallNodeEntryNodeTuples);
}

enum ReturnStateMergingStrategy {
	MERGE_IF_AT_SAME_PROGPOS_AND_HAVE_SAME_PROGRAVS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
				Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos) {
			return otherReturnNodesAtSameProgPos;
		}
	},
	
	MERGE_IF_AT_SAME_PROGPOS_AND_HAVE_SAME_PROGRAVS_AND_HAVE_SAME_NUMBER_OF_ALLOCATIONS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
				Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos) {
			LLVMAbstractState returnState = returnNode.getObject();
			return otherReturnNodesAtSameProgPos
					.stream()
					.filter(n -> LLVMIntersectionHeuristics.haveMatchingStacks(n.getObject(), returnState, true))
					.filter(n -> n.getObject().getAllocations().size() == returnState.getAllocations().size())
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},

	MERGE_IF_REACHABLE_FROM_SAME_ENTRY_NODE_WITHOUT_STEPPING_OVER_CALL_ABSTRACTION {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
				Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos) {
			Set<Node<LLVMAbstractState>> entryNodes = fg.getEntryNodes();
			return otherReturnNodesAtSameProgPos
					.stream()
					.filter(createReachabilityPredicate(fg,entryNodes,returnNode))
					.collect(Collectors.toCollection(LinkedHashSet::new));
			
					
		}
	},
	MERGE_IF_REACHABLE_FROM_SAME_ENTRY_NODE_WITHOUT_STEPPING_OVER_CALL_ABSTRACTION_MUST_HAVE_SAME_NUMBER_OF_ALLOCATIONS {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
				Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos) {
			Set<Node<LLVMAbstractState>> entryNodes = fg.getEntryNodes();
			LLVMAbstractState returnState = returnNode.getObject();
			return otherReturnNodesAtSameProgPos
					.stream()
					.filter(createReachabilityPredicate(fg, entryNodes, returnNode))
					.filter(n -> n.getObject().getAllocations().size() == returnState.getAllocations().size())
					.collect(Collectors.toCollection(LinkedHashSet::new));
		}
	},
	
	NEVER_MERGE {
		@Override
		Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
				Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos) {
			return Collections.emptySet();
		}
	};
	
	Predicate<Node<LLVMAbstractState>> createReachabilityPredicate(LLVMFunctionGraph fg,Set<Node<LLVMAbstractState>> entryNodes, Node<LLVMAbstractState> returnNode) {
		return (node -> entryNodes
				.stream()
				.anyMatch(en -> fg.getGraph().hasPath(en,node,false,dontFollowCallAbstractionsFilter)
						&& fg.getGraph().hasPath(en,returnNode,false,dontFollowCallAbstractionsFilter)));
	}
	
	
	EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> dontFollowCallAbstractionsFilter = 
			(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest, LLVMEdgeInformation label) -> !(label instanceof LLVMCallAbstractionEdge);

	
	
	/**
	 * 
	 * @param fg
	 * @param returnNode
	 * @param otherReturnNodesAtSameProgPos Set of nodes n != otherReturnNodesAtSameProgPos which are at the same program position
	 * and have the same program variables
	 * @return
	 */
	abstract Set<Node<LLVMAbstractState>> mustMergeWith(LLVMFunctionGraph fg, Node<LLVMAbstractState> returnNode,
			Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPos);
}


}
