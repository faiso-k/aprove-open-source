package aprove.input.Programs.llvm.segraph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author Hermann Walth A path in the LLVM symbolic execution graph
 */
//TODO: repace backtrackPath by the path findig methods in SimpleGraph?
public class LLVMSEPath extends ArrayList<Node<LLVMAbstractState>> implements LLVMGraphSection {

	/**
	 * Serialise me!
	 */
	private static final long serialVersionUID = 412113394205570766L;

	private Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> renamingsClassesAlongPath;

	private Map<LLVMAllocation, LLVMAllocation> renamingsOfAllocationsAlongPath;

	/**
	 * Find all paths from the root node to the target node
	 * 
	 * @param graph
	 *            The graph to find paths in
	 * @param target
	 *            The node to find paths to
	 * @return The list of paths from the graph's root to target
	 */
	public static List<LLVMSEPath> backtrackPath(LLVMSEGraph graph, Node<LLVMAbstractState> target) {
		return LLVMSEPath.backtrackPath(graph, graph.getRoot(), target);
	}

	/**
	 * Find all paths from the start node to the target node
	 * 
	 * @param graph
	 *            The graph to find paths in
	 * @param start
	 *            The node to find paths from
	 * @param target
	 *            The node to find paths to
	 * @return The list of paths from the start to the target
	 */
	public static List<LLVMSEPath> backtrackPath(LLVMSEGraph graph, Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> target) {
		return LLVMSEPath.backtrackPath(graph, start, target, Collections.emptySet(), Collections.emptySet());
	}

	/**
	 * Find all paths from the start node to the target node
	 * 
	 * @param graph
	 *            The graph to find paths in
	 * @param start
	 *            The node to find paths from
	 * @param target
	 *            The node to find paths to
	 * @param edgeTypesNotToTraverse
	 *            Edges whose type is included here will be ignored
	 * @return The list of paths from the start to the target
	 */
	public static List<LLVMSEPath> backtrackPath(LLVMSEGraph graph, Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> target, Set<Class<? extends LLVMEdgeInformation>> edgeTypesNotToTraverse) {
		return LLVMSEPath.backtrackPath(graph, start, target, edgeTypesNotToTraverse, Collections.emptySet());
	}

	/**
	 * Find all paths from the start node to the target node
	 * 
	 * @param graph
	 *            The graph to find paths in
	 * @param start
	 *            The node to find paths from
	 * @param target
	 *            The node to find paths to
	 * @param visited
	 *            The set of nodes already seen by this method, used in
	 *            recursion
	 * @return The list of paths from the start to the target
	 */
	private static List<LLVMSEPath> backtrackPath(LLVMSEGraph graph, Node<LLVMAbstractState> start,
			Node<LLVMAbstractState> target, Set<Class<? extends LLVMEdgeInformation>> edgeTypesNotToFollow,
			Set<Node<LLVMAbstractState>> visited) {
		List<LLVMSEPath> result = new LinkedList<>();
		visited = new LinkedHashSet<>(visited);
		visited.add(target);
		if (target.equals(start)) {
			LLVMSEPath path = new LLVMSEPath(graph);
			path.add(target);
			result.add(path);
			return result;
		}
		outer: for (Edge<LLVMEdgeInformation, LLVMAbstractState> inEdge : graph.getInEdges(target)) {
			Node<LLVMAbstractState> parent = inEdge.getStartNode();
			for (Class<? extends LLVMEdgeInformation> edgeClass : edgeTypesNotToFollow) {
				if (edgeClass.isInstance(inEdge.getObject())) {
					continue outer;
				}
			}

			if (!visited.contains(parent)) {
				for (LLVMSEPath path : LLVMSEPath.backtrackPath(graph, start, parent, edgeTypesNotToFollow, visited)) {
					path.add(target);
					result.add(path);
				}
			}
		}
		return result;
	}

	/**
	 * The graph where the path comes from
	 */
	//FIXME change back to LLVMSEGraph later? right now, very  ugly casts to LLVMSEGrap here in the class
	private SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph;

	/**
	 * create a path from a list of nodes
	 * 
	 * @param nodes
	 *            a list of nodes representing the path
	 */
	public LLVMSEPath(List<Node<LLVMAbstractState>> nodes, SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> graph) {
		super(nodes);
		this.graph = graph;
	}

	/**
	 * create an empty path
	 */
	private LLVMSEPath(LLVMSEGraph graph) {
		super();
		this.graph = graph;
	}

	public static LLVMSEPath mergePathsWithOverlappingEndAndStart(LLVMSEPath firstPath, LLVMSEPath secondPath) {
		if (firstPath.getLast() != secondPath.getFirst() || firstPath.graph != secondPath.graph) {
			throw new IllegalArgumentException();
		}

		ArrayList<Node<LLVMAbstractState>> newNodes = new ArrayList<>(firstPath);
		Iterator<Node<LLVMAbstractState>> it = secondPath.iterator();

		it.next(); // Discard first node

		while (it.hasNext()) {
			newNodes.add(it.next());
		}

		return new LLVMSEPath(newNodes, firstPath.graph);

	}

	/**
	 * This is what's wrong with aprove
	 * 
	 * @author not me, don't ask
	 * @return The set of pairs of allocation pairs collected from each state in
	 *         the path. These are needed to ensure that each pair of
	 *         allocations is distinct.
	 */
	public Set<ImmutablePair<LLVMAllocation, LLVMAllocation>> getAllocationPairs() {
		Set<ImmutablePair<LLVMAllocation, LLVMAllocation>> result = new LinkedHashSet<>();
		for (Node<LLVMAbstractState> node : this) {
			LLVMAbstractState state = node.getObject();
			for (LLVMAllocation alloc1 : state.getAllocations()) {
				for (LLVMAllocation alloc2 : state.getAllocations()) {
					if (!alloc1.equals(alloc2)) {
						result.add(new ImmutablePair<>(alloc1, alloc2));
					}
				}
			}
		}
		return result;
	}

	/**
	 * Collect all relation constraints along the path. These constraints
	 * include: The constraints for each individual node in the path, all state
	 * change information along the edges, equalities of renamed references
	 * along instance edges. A model satisfying these constraints represents a
	 * set of concrete states linked by the path edges
	 * 
	 * @return The set of all relation constraints along the path. This does not
	 *         include those constraints not expressible as a single relation.
	 */
	public IntegerRelationSet getConstraints() {
		final LLVMRelationFactory factory = ((LLVMSEGraph)this.graph).getStrategyParameters().SMTsolver.stateFactory
				.getRelationFactory();
		IntegerRelationSet constraints = new IntegerRelationSet();
		for (Node<LLVMAbstractState> node : this) {
			constraints.addAll(node.getObject().getIntegerState().toRelationSet());
		}
		for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getEdges()) {
			LLVMEdgeInformation label = edge.getObject();
			constraints.addAll(label.getChangesOnEdge());
			// TODO adding equations for the substitution is ok for
			// non-termination, but it would be more precise to
			// use the substitution as a substitution - see also LLVMSELoop
			if (label instanceof LLVMInstantiationInformation) {
				constraints.addAll(LLVMRelation.toSetOfEquations(
						((LLVMInstantiationInformation) label).getReferenceCorrespondenceMap(), factory));
			}
		}
		return constraints;
	}

	/**
	 * Collect the edges of this path
	 * 
	 * @return The list of edges connecting the nodes of this path
	 */
	@Override
	public List<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges() {
		List<Edge<LLVMEdgeInformation, LLVMAbstractState>> result = new LinkedList<>();
		Node<LLVMAbstractState> predecessor = null;
		for (Node<LLVMAbstractState> node : this) {
			if (predecessor != null) {
				result.add(this.graph.getEdge(predecessor, node));
			}
			predecessor = node;
		}
		return result;
	}

	/**
	 * @param interestingRefs
	 *            The interesting references.
	 * @return True if this path contains a load instruction producing an
	 *         interesting reference and this reference is fresh. False
	 *         otherwise.
	 */
	public boolean hasUnknownLoad(Set<IntegerVariable> interestingRefs) {
		LLVMAbstractState prevState = null;
		LLVMLoadInstruction load = null;
		for (Node<LLVMAbstractState> node : this) {
			LLVMAbstractState state = node.getObject();
			if (prevState == null) {
				LLVMInstruction instr = state.getCurrentInstruction();
				if (instr instanceof LLVMLoadInstruction) {
					prevState = state;
					load = (LLVMLoadInstruction) instr;
				}
			} else {
				if (interestingRefs.contains(state.getSymbolicVariableForProgramVariable(load.getProducedVariable()))) {
					LLVMSimpleTerm ref = prevState.getSimpleTermForLiteral(load.getAddressValue());
			        boolean unsigned = false;
			        if (state.getStrategyParamters().useBoundedIntegers) {
			            unsigned = state.getModule().getUnsignedBitvectorVariables().contains(load.getIdentifier().getName());
			        }
					if (ref == null || prevState.getMemory()
							.get(new LLVMMemoryRange(ref, ref, load.getAddressValue().getType(), unsigned)) == null) {
						return true;
					}
				}
				prevState = null;
				load = null;
			}
		}
		return false;
	}

	
	
	
	//do not modify returned set
	@Deprecated /* done in variable tracker now */
	private Set<LLVMSymbolicVariable> getRenamingsOfSingleVariableOnSingleEdge(int indexOnThisPathOfStartNodeOfEdge, LLVMSymbolicVariable var ) {
		if(Globals.useAssertions) {
			assert indexOnThisPathOfStartNodeOfEdge < size() -1;
		}
		
		if(var instanceof LLVMHeuristicConstRef ) {
			return Collections.singleton(var);
		}
		
		Node<LLVMAbstractState> currentNode = this.get(indexOnThisPathOfStartNodeOfEdge);
		Node<LLVMAbstractState> nextNode = this.get(indexOnThisPathOfStartNodeOfEdge + 1);
		LLVMEdgeInformation edgeToNextNode = graph.getEdgeObject(currentNode, nextNode);
		
		if(edgeToNextNode instanceof LLVMInstantiationInformation) {
			LLVMInstantiationInformation instantiationEdge = (LLVMInstantiationInformation) edgeToNextNode;
			Map<LLVMSimpleTerm, LLVMSimpleTerm> referenceCorrespondenceMap = instantiationEdge
					.getReferenceCorrespondenceMap();

			Set<LLVMSymbolicVariable> variablesInTarget = new LinkedHashSet<>();
			for (Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : referenceCorrespondenceMap.entrySet()) {
				LLVMSimpleTerm currentKey = entry.getKey();
				if (entry.getValue().equals(var)) {
					if(currentKey instanceof LLVMSymbolicVariable) {
					variablesInTarget.add( (LLVMSymbolicVariable) currentKey);
					} else {
						throw new IllegalStateException("Strange type");
					}
				}
			}
			return variablesInTarget;
		} else {
			Set<LLVMSymbolicVariable> variablesInNextState = nextNode.getObject().getSymbolicVariables();
			Set<LLVMSymbolicVariable> result = new LinkedHashSet<>();
			if (variablesInNextState.contains(var)) {
				result.add(var);
			}
			LLVMAbstractState currentState =  currentNode.getObject();
			LLVMAbstractState nextState =  nextNode.getObject();
			if((edgeToNextNode instanceof LLVMEvaluationInformation && !(currentState.getCurrentInstruction() instanceof LLVMAssignmentInstruction) ) 
					|| edgeToNextNode instanceof LLVMRefinementInformation ) {
				//There was no reassignment of a variable -> If some %x is bound to v in the first and w in the next state, this indicates a renaming from v to w
				for(Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> entry : currentState.getProgramVariables().entrySet() ) {
					if(entry.getValue().x.equals(var)) {
						ImmutablePair<LLVMSymbolicVariable, LLVMType> progVarEntryNextState = nextState.getProgramVariables().get(entry.getKey());
						if(progVarEntryNextState != null && entry.getValue().y.equals(progVarEntryNextState.y) ) {
							result.add(progVarEntryNextState.x);
						}
					}
				}
			}
			return result;
		}
	}
	
	@Deprecated /* done in variable tracker now */
	private ArrayList<Set<LLVMSymbolicVariable>> createRenamingOfVariableEquivalenceClass(Set<LLVMSymbolicVariable> equivalenceClassInFirstState, LLVMRelationFactory relFactory, Abortion aborter)  {
		int pathLength = this.size() - 1;
		ArrayList<Set<LLVMSymbolicVariable>> renamingsList = new ArrayList<>(pathLength);
		
		renamingsList.add(equivalenceClassInFirstState);
		
		Set<LLVMSymbolicVariable> currentSet = equivalenceClassInFirstState;
		
		for (int i = 0; i < pathLength; i++) {
			Set<LLVMSymbolicVariable> nextSet = new LinkedHashSet<>();
			LLVMAbstractState nextState = get(i+1).getObject();
			for(LLVMSymbolicVariable varOfCurrentClass : currentSet) {
				nextSet.addAll(getRenamingsOfSingleVariableOnSingleEdge(i, varOfCurrentClass));
			}
			
			extendVariableEquivalenceClass(nextState, nextSet, relFactory, aborter);
			
			renamingsList.add(nextSet);
			currentSet = nextSet;
		}
		
		
		return renamingsList;
	}
	
	@Deprecated /* done in variable tracker now */
	private static Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> getVariableEquivalenceClassesOfState(LLVMAbstractState state, Abortion aborter) {
		Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> varsToClasses = new LinkedHashMap<>();
		
		for(LLVMSymbolicVariable varOfState : state.getSymbolicVariables()) {
			if(!varsToClasses.containsKey(varOfState)) {
				ImmutableSet<LLVMSymbolicVariable> classForCurrentVar = state.getEquivalenceclassOfSymbolicVariable(varOfState,aborter);
				
				for(LLVMSymbolicVariable memberOfClass : classForCurrentVar) {
					Set<LLVMSymbolicVariable> previousEntry = varsToClasses.put(memberOfClass, classForCurrentVar);
					if(previousEntry != null) {
						throw new IllegalStateException("Inconsistent variable equivalence classes");
					}
				}
			}
			
		}
		
		return varsToClasses;
	}
	
	@Deprecated /* done in variable tracker now */
	public Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> getSymbolicVariableRenamingsOfEachStepIncludingEqualities(
			LLVMRelationFactory relFactory, Abortion aborter) {
		if (this.renamingsClassesAlongPath == null) {
			Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> variablesToTheirEquivalenceClasses = getVariableEquivalenceClassesOfState(getFirst().getObject(),aborter);
			
			Map<Set<LLVMSymbolicVariable>, ArrayList<Set<LLVMSymbolicVariable>>> classesToRenamingLists = new LinkedHashMap<>();
			
			for(Set<LLVMSymbolicVariable> equivalenceClass : variablesToTheirEquivalenceClasses.values()) {
				classesToRenamingLists.put(equivalenceClass, createRenamingOfVariableEquivalenceClass(equivalenceClass,relFactory,aborter));
			}
			
			Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> resultMap = new LinkedHashMap<>();
			
			for(Map.Entry<LLVMSymbolicVariable, Set<LLVMSymbolicVariable>> entry : variablesToTheirEquivalenceClasses.entrySet()) {
				resultMap.put(entry.getKey(), classesToRenamingLists.get(entry.getValue()));
			}
			
			this.renamingsClassesAlongPath = resultMap;
		}

		return this.renamingsClassesAlongPath;
	}
	
	/*@Deprecated
	private ArrayList<LLVMSymbolicVariable> createRenamingListForSingleVariable(int indexOfNodeToStartAt,
			LLVMSymbolicVariable variableOfFirstStateInSubPath) {
		int pathLength = this.size() - 1;
		ArrayList<LLVMSymbolicVariable> renamingsList = new ArrayList<>(pathLength);
		renamingsList.add(variableOfFirstStateInSubPath);

		LLVMSymbolicVariable curentRenamingOfVariable = variableOfFirstStateInSubPath;
		for (int i = indexOfNodeToStartAt; i < pathLength; i++) {
			Node<LLVMAbstractState> currentNode = this.get(i);
			Node<LLVMAbstractState> nextNode = this.get(i + 1);
			LLVMEdgeInformation edgeToNextNode = graph.getEdgeObject(currentNode, nextNode);
			if (curentRenamingOfVariable != null) {
				if (edgeToNextNode instanceof LLVMInstantiationInformation) {
					LLVMInstantiationInformation instantiationEdge = (LLVMInstantiationInformation) edgeToNextNode;
					Map<LLVMSimpleTerm, LLVMSimpleTerm> referenceCorrespondenceMap = instantiationEdge
							.getReferenceCorrespondenceMap();

					List<LLVMSimpleTerm> variablesInTarget = new ArrayList<>();
					for (Map.Entry<LLVMSimpleTerm, LLVMSimpleTerm> entry : referenceCorrespondenceMap.entrySet()) {
						LLVMSimpleTerm currentKey = entry.getKey();
						if (entry.getValue().equals(curentRenamingOfVariable)
								&& !(currentKey instanceof LLVMHeuristicConstRef)) {
							variablesInTarget.add(currentKey);
						}
					}
					if (variablesInTarget.size() > 1)
						throw new IllegalStateException("Ambiguous mapping");
					else if (variablesInTarget.isEmpty()) {
						curentRenamingOfVariable = null;
					} else {
						LLVMSimpleTerm renamingResult = variablesInTarget.get(0);
						if (renamingResult instanceof LLVMSymbolicVariable) {
							curentRenamingOfVariable = (LLVMSymbolicVariable) renamingResult;
						} else {
							curentRenamingOfVariable = null;
						}
					}
				} else {
					Set<LLVMSymbolicVariable> variablesInNextState = nextNode.getObject().getSymbolicVariables();
					if (variablesInNextState.contains(curentRenamingOfVariable)) {
						// pass
					} else {
						String.format("Lost variable %s on edge from node %d to node %d, edge type: %s",
								curentRenamingOfVariable.getName(), currentNode.getNodeNumber(),
								nextNode.getNodeNumber(), edgeToNextNode.getClass().getName());
						curentRenamingOfVariable = null;
					}
				}
			}
			renamingsList.add(curentRenamingOfVariable);
		}

		return renamingsList;
	}*/

	/**
	 * Returns a mapping v -> [{...},{...},{...} ] where each entry in the list
	 * represents one renaming step on the path. Each set in the list contains
	 * an equivalence class of variables of the respective state
	 */
	/*@Deprecated
	public Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> getSymbolicVariableRenamingsOfEachStepIncludingEqualitiesOld(
			LLVMRelationFactory relFactory, Abortion aborter) {
		if (this.renamingsClassesAlongPath == null) {
			Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> resultMapping = new LinkedHashMap<>();
			Set<LLVMSymbolicVariable> allVariablesOfFirstState = this.get(0).getObject().getSymbolicVariables();

			for (LLVMSymbolicVariable variableOfFirstState : allVariablesOfFirstState) {
				resultMapping.put(variableOfFirstState, createRenamingListForSingleVariableIncludingEqualities(
						variableOfFirstState, relFactory, aborter));
			}
			this.renamingsClassesAlongPath = resultMapping;
		}

		return this.renamingsClassesAlongPath;
	}*/

	/*@Deprecated
	private ArrayList<Set<LLVMSymbolicVariable>> createRenamingListForSingleVariableIncludingEqualities(
			LLVMSymbolicVariable variableOfFirstState, LLVMRelationFactory relFactory, Abortion aborter) {
		ArrayList<Set<LLVMSymbolicVariable>> resultList = createInitialRenamingListForSingleVariable(
				variableOfFirstState);

		for (int i = 0; i < this.size(); i++) {
			LLVMAbstractState currentState = this.get(i).getObject();
			extendVariableEquivalenceClass(currentState, resultList.get(i), relFactory, aborter);

			for (LLVMSymbolicVariable variableFromEquivalenceClass : resultList.get(i)) {
				ArrayList<LLVMSymbolicVariable> renamingListFromCurrentStateOn = createRenamingListForSingleVariable(i,
						variableFromEquivalenceClass);
				mergeNewRenamingIntoList(resultList, renamingListFromCurrentStateOn);
			}
		}

		return resultList;

	}*/
	
	@Deprecated /* done in variable tracker now */
	private void extendVariableEquivalenceClass(LLVMAbstractState stateVariablesBelongTo,
			Set<LLVMSymbolicVariable> variablesKnownToBeEqualInState, LLVMRelationFactory relFactory,
			Abortion aborter) {
		
		//variablesKnownToBeEqualInState.addA
		Set<LLVMSymbolicVariable> allVariablesOfState = stateVariablesBelongTo.getSymbolicVariables();
		boolean madeChange = true;
		
		//We don't entirely rely on equivalences being  detected transitively by the SMT backend.
		//In particular because we may have detected the entries of variablesKnownToBeEqualInState via a path analysis, not just the knowledge in a particular state
		outerLoop: while (madeChange) {
			madeChange = false;
			for (LLVMSymbolicVariable equivalenceClassMember : variablesKnownToBeEqualInState) {
				madeChange = variablesKnownToBeEqualInState
						.addAll(stateVariablesBelongTo.getEquivalenceclassOfSymbolicVariable(equivalenceClassMember,aborter));
				if (madeChange)
					continue outerLoop;
			}
		}
	}

	/*@Deprecated
	private ArrayList<Set<LLVMSymbolicVariable>> createInitialRenamingListForSingleVariable(LLVMSymbolicVariable v) {
		ArrayList<Set<LLVMSymbolicVariable>> result = new ArrayList<>();
		LinkedHashSet<LLVMSymbolicVariable> firstEntry = new LinkedHashSet<>();
		firstEntry.add(v);
		result.add(firstEntry);
		for (int i = 1; i < this.size(); i++) {
			result.add(new LinkedHashSet<>());
		}

		return result;
	}*/

	/*@Deprecated
	private void mergeNewRenamingIntoList(ArrayList<Set<LLVMSymbolicVariable>> existingRenamingSetList,
			ArrayList<LLVMSymbolicVariable> newRenamingListForSingleVariable) {
		if (newRenamingListForSingleVariable.size() > existingRenamingSetList.size())
			throw new IllegalArgumentException(
					"The list to merge into the existing list must be smaller than the existing list");

		int startIndex = existingRenamingSetList.size() - newRenamingListForSingleVariable.size();
		for (int indexExistingList = startIndex; indexExistingList < existingRenamingSetList
				.size(); indexExistingList++) {
			int indexNewList = indexExistingList - startIndex;

			LLVMSymbolicVariable variableFromNewList = newRenamingListForSingleVariable.get(indexNewList);
			if (variableFromNewList == null) {
				// There are no more renamings
				break;
			}

			Set<LLVMSymbolicVariable> setInExistingListCorrespondingToCurrentStep = existingRenamingSetList
					.get(indexExistingList);
			setInExistingListCorrespondingToCurrentStep.add(variableFromNewList);
		}
	}/*

	/**
	 * This implements the predicate "not_deallocated" from the LLVM Recursion Paper
	 * 
	 * @param allocationInFirstState
	 * @param relFactory
	 * @param aborter
	 * @return A pair <x,y> such that x is true if we can prove that the malloc or stack allocation
	 *         <code>allocationInFirstState</code> of the first state on the
	 *         path is not deallocated/released on this path.
	 *         If x is true, y == true indicates that the allocation was lost during a generalization
	 */
	public Pair<Boolean,Boolean> notDeallocated(LLVMAllocation allocationInFirstState, LLVMRelationFactory relFactory,
			Abortion aborter) {
		return notDeallocatedUntil(allocationInFirstState, size() - 1, relFactory, aborter  );
	}
	
	
	/**
	 * returns A pair <x,y> such that x is true if we can prove that the malloc or stack allocation
	 *         <code>allocationInFirstState</code> of the first state on the
	 *         path is not deallocated/released on this path up to position <code>targetStateIndex</code>.
	 *         If x is true, y == true indicates that the allocation was lost during a generalization
	 */

	private Pair<Boolean,Boolean> notDeallocatedUntil(LLVMAllocation allocationInFirstState, int targetStateIndex, LLVMRelationFactory relFactory,
			Abortion aborter) {
		LLVMAbstractState firstState = this.getFirst().getObject();
		if (!firstState.getAllocations().contains(allocationInFirstState))
			throw new IllegalArgumentException("Given allocation is not allocated in first state of path");

		if(size() == 1)
			return new Pair<>(true,false);
		
		if (firstState.getAllocatedByMalloc().contains(allocationInFirstState)) {
			for (int stateIndex = 0; stateIndex < targetStateIndex; stateIndex++) {

				if(isAllocationLostOnPathAtIndex(allocationInFirstState,stateIndex, relFactory, aborter)) {
					return new Pair<>(true,true); //We can exit here
				} else if(isHarmlessEdgeCaseOfNotDeallocated(allocationInFirstState,stateIndex, relFactory, aborter)) {
					continue;
				} else if(isHarmlessFreeCaseOfNotDeallocated(allocationInFirstState,stateIndex, relFactory, aborter )) {
					continue;
				} else if(isHarmlessFunctionSkipCaseOfNotDeallocated(allocationInFirstState,stateIndex, relFactory, aborter)) {
					continue;
				}
				return new Pair<>(false,false); //If we got here, the predicate does not hold
			}
			return new Pair<>(true,false);
		} else {
			//Check if we ever return from the topmost frame during the path
			if(calculateStackChangeDifference() >= 0) {
				//Check if we lose the allocation on the path
				for (int stateIndex = 0; stateIndex < targetStateIndex; stateIndex++) {
					if(isAllocationLostOnPathAtIndex(allocationInFirstState,stateIndex, relFactory, aborter)) {
						return new Pair<>(true,true); //We can exit here
					}
				}
				return new Pair<>(true,false); //The allocation was not deallocated and we also did not lose it on the path
			} else {
				return new Pair<>(false,false); //The allocation was deallocated
			}
			
		}
	}


	
	/**
	 * Returns true if this edge is "harmless" w.r.t. determining the predicate not_deallocated, i.e. if we have one of the cases were we don't have to check something
	 */
	private boolean isHarmlessEdgeCaseOfNotDeallocated(LLVMAllocation allocationInFirstState, int stateIndex,  LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);

		LLVMAbstractState currentState = currentNode.getObject();
		LLVMInstruction currentInstruction = currentState.getCurrentInstruction();
		
		
		if(edgeLabelCurrentToNext instanceof LLVMInstantiationInformation || edgeLabelCurrentToNext instanceof LLVMRefinementInformation || edgeLabelCurrentToNext instanceof LLVMCallAbstractionEdge) {
			return true;
		}
		if (edgeLabelCurrentToNext instanceof LLVMEvaluationInformation) {
			if (currentInstruction instanceof LLVMCallInstruction) {
				LLVMCallInstruction previousCall = (LLVMCallInstruction) currentInstruction;
				return !previousCall.isFreeCall();
			} else {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Returns true iff we perform a free from <code>stateIndex<code/> to <code>stateIndex+1<code/>, but we can prove that we do not free <code>allocationInFirstState</code>.
	 */
	private boolean isHarmlessFreeCaseOfNotDeallocated(LLVMAllocation allocationInFirstState, int stateIndex,  LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);

		LLVMAbstractState currentState = currentNode.getObject();
		LLVMInstruction currentInstruction = currentState.getCurrentInstruction();
		
		if (edgeLabelCurrentToNext instanceof LLVMEvaluationInformation
				&& currentInstruction instanceof LLVMCallInstruction) {
			LLVMCallInstruction callInstruction = (LLVMCallInstruction) currentInstruction;
			if (callInstruction.isFreeCall() ) {
				if(callInstruction.isGuaranteedToBeFreeOfNullPointer(currentState,
					relFactory.getTermFactory())) {
					return true; //Freeing NULL is harmless
				}
				
				
				int freedAllocationIndex = callInstruction.getIndexOfFreedAllocation(currentState,
						currentNode.getNodeNumber(),aborter).x;
				if (freedAllocationIndex < 0)
					throw new IllegalStateException(
							"Illegal free, should have already been caught during graph construction!");
				LLVMAllocation freedAllocation = currentState.getAllocations().get(freedAllocationIndex);

				if(Globals.useAssertions) {
					Set<LLVMAllocation> allocDiff = new LinkedHashSet<LLVMAllocation>(currentState.getAllocatedByMalloc());
					allocDiff.removeAll(nextNode.getObject().getAllocatedByMalloc());
					assert allocDiff.size() == 1 && allocDiff.contains(freedAllocation): "The resulting set should exactly contain the freedAllocation";
				}
				
				//Freeing an allocation disjoint from the one we are interested in is harmless
				return disjoint(allocationInFirstState, stateIndex, freedAllocation, relFactory, aborter);
			}
		}
		
		return false;
	}
	
	/**
	 * Returns true iff the edge between <code>stateIndex<code/> to <code>stateIndex+1<code/> 
	 * is a function skip edge whose label tells us that it does not deallocate <code>allocationInFirstState</code>. 
	 */
	private boolean isHarmlessFunctionSkipCaseOfNotDeallocated(LLVMAllocation allocationInFirstState, int stateIndex,  LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);

		
		if(edgeLabelCurrentToNext instanceof LLVMMethodSkipEdge) {
			LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edgeLabelCurrentToNext;
			
			LLVMIntermediateIntersectionResult intersectionResult = skipEdge.getIntersectionResultOld();
			Set<LLVMAllocation> setOfNotDeallocatedCallStateAllocations = intersectionResult.getPreserverdMallocAllocationsOfCallState();
			
			LLVMAllocation renamedAllocation = getRenamingsOfAllocation(stateIndex+1, allocationInFirstState, relFactory, aborter).get(stateIndex);
			
			if(renamedAllocation != null && setOfNotDeallocatedCallStateAllocations.contains(renamedAllocation) ) {
				if(Globals.useAssertions) {
					assert nextNode.getObject().getAllocations().contains(renamedAllocation);
				}
				
				//We are stepping over a function skip edge whose label tells us that it does not deallocate the given allocation
				return true;
			}
			
			
		}
		
		
		return false;
	}
	
	
	/**
	 * Returns true iff we can prove that all allocations of the node at <code>targetNodeIndex</code> are disjoint from <code>allocationOfFirstState</code>
	 */
	private boolean isAllocationLostOnPathAtIndex(LLVMAllocation allocationOfFirstState, int targetNodeIndex, LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> targetNode = get(targetNodeIndex);
		if(Globals.useAssertions) {
			assert getFirst().getObject().getAllocations().contains(allocationOfFirstState);
		}
		if(targetNode == getFirst()) {
			return false; //This is by definition (and the check above makes sure it holds) 
		}
		
		LLVMAbstractState targetState = targetNode.getObject();
		List<LLVMAllocation> allocationsCopy = new ArrayList<>(targetState.getAllocations()); //Workaround for bug in immutables breaking .stream()
		return allocationsCopy.
				stream().
				allMatch(allocation -> disjoint(allocationOfFirstState, targetNodeIndex, allocation, relFactory, aborter));
		
	}
	

	/**
	 * Implements the predicate "disjoint" from the LLVM Recursion Paper
	 * 
	 * Returns true iff we can prove that the allocation <code>allocationInFirstState</code> of the first state in this path is disjoint from the allocation
	 * <code>lastStateAllocation</code> of the last state on this path
	 * 
	 * @param allocationInFirstState
	 * @param lastStateAllocation
	 * @param relFactory
	 * @param aborter
	 * @return
	 */
	public boolean disjoint(LLVMAllocation allocationInFirstState, LLVMAllocation lastStateAllocation,
			LLVMRelationFactory relFactory, Abortion aborter) {
		return disjoint(allocationInFirstState, this.size() - 1, lastStateAllocation, relFactory, aborter);
	}

	private boolean disjoint(LLVMAllocation allocationInFirstState, int targetStateIndex,
			LLVMAllocation targetStateAllocation, LLVMRelationFactory relFactory, Abortion aborter) {
		if (!getFirst().getObject().getAllocations().contains(allocationInFirstState)
				|| !get(targetStateIndex).getObject().getAllocations().contains(targetStateAllocation))
			throw new IllegalArgumentException("Allocations do not satisfy contract");

		if (existsAllocatingInstructionResultingInGivenAllocationDisjointFromFirstStateAllocation(allocationInFirstState, targetStateIndex, targetStateAllocation, relFactory,
				aborter))
			return true;

		if (existsStateWithDisjointInitialAndTargetAllocation(allocationInFirstState, targetStateIndex,
				targetStateAllocation, relFactory, aborter))
			return true;

		return false;
	}

	/**
	 * This implements the predicate "unchanged" from the LLVM Recursion Paper.
	 * However, we do not check that unchanged heap ranges must also be part of allocations that are not deallocated.
	 * This must be done later to ensure full compability with the definition of the predicate as done in the paper.
	 * 
	 * @param memoryRangeOfFirstState
	 *            A MemoryRange from the heap of the first state on this path
	 * @param correspondingAllocation
	 *            The allocation containing <code>memoryRangeOfFirstState</code>
	 * @return True if we can guarantee that the given MemoryRange was not
	 *         modified on this path
	 */
	public boolean unchanged(LLVMMemoryRange memoryRangeOfFirstState, LLVMAllocation correspondingAllocation,
			LLVMRelationFactory relFactory, Abortion aborter) {
		int indexOfLastNode = this.size() - 1;

		if (!(memoryRangeOfFirstState.getFromRef() instanceof LLVMSymbolicVariable
				&& memoryRangeOfFirstState.getToRef() instanceof LLVMSymbolicVariable))
			throw new IllegalArgumentException("Boundaries of the given range must be symbolic variables");

		
		if(this.size() == 1) {
			return true; // By definition
		}
		

		for (int stateIndex = 0; stateIndex < indexOfLastNode; stateIndex++) {
			Node<LLVMAbstractState> currentNode = this.get(stateIndex);
			Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);


			if(isAllocationLostOnPathAtIndex(correspondingAllocation,stateIndex, relFactory, aborter)) {
				return true;
			} else if(isHarmlessEdgeCaseOfUnchanged(correspondingAllocation, stateIndex, relFactory, aborter)) {
				continue;
			} else if(isHarmlessStoreCaseOfUnchanged(correspondingAllocation,memoryRangeOfFirstState, stateIndex, relFactory, aborter)) {
				continue;
			} else if(isHarmlessFunctionSkipEdgeCaseOfUnchanged(correspondingAllocation, memoryRangeOfFirstState, stateIndex, relFactory, aborter)) {
				continue;
			}
			return false;

		}
		return true;
	}
	
	
	private boolean isHarmlessEdgeCaseOfUnchanged(LLVMAllocation allocationOfFirstState, int stateIndex, LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);

		LLVMAbstractState currentState = currentNode.getObject();
		LLVMInstruction currentInstruction = currentState.getCurrentInstruction();
		
		
		if(edgeLabelCurrentToNext instanceof LLVMInstantiationInformation || edgeLabelCurrentToNext instanceof LLVMRefinementInformation || edgeLabelCurrentToNext instanceof LLVMCallAbstractionEdge) {
			return true;
		}
		if(edgeLabelCurrentToNext instanceof LLVMEvaluationInformation && !(currentInstruction instanceof LLVMStoreInstruction)) {
			return true;
		}
		return false;
	}
	
	/**
	 * Returns true iff <code>stateIndex</code> is at a store for which we can prove that it does not affect the renaming of <code>memoryRangeOfFirstState</code> in that state
	 * 
	 */
	private boolean isHarmlessStoreCaseOfUnchanged(LLVMAllocation allocationOfFirstState, LLVMMemoryRange memoryRangeOfFirstState, int stateIndex, LLVMRelationFactory relFactory, Abortion aborter) {
		
		
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);
		
		LLVMAbstractState currentState = currentNode.getObject();
		LLVMInstruction currentInstruction = currentState.getCurrentInstruction();
		
		if(edgeLabelCurrentToNext instanceof LLVMEvaluationInformation && currentInstruction instanceof LLVMStoreInstruction) {
		
			if (!(memoryRangeOfFirstState.getFromRef() instanceof LLVMSymbolicVariable
					&& memoryRangeOfFirstState.getToRef() instanceof LLVMSymbolicVariable))
				throw new IllegalArgumentException("Boundaries of the given range must be symbolic variables");
			
		LLVMSymbolicVariable lowerBoundOfRange = (LLVMSymbolicVariable) memoryRangeOfFirstState.getFromRef();
		LLVMSymbolicVariable upperBoundOfRange = (LLVMSymbolicVariable) memoryRangeOfFirstState.getToRef();
		
		Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> renamings = getSymbolicVariableRenamingsOfEachStepIncludingEqualities(relFactory, aborter);
		
		Set<LLVMSymbolicVariable> equivalenceClassForLowerBound = renamings.get(lowerBoundOfRange)
				.get(stateIndex);
		Set<LLVMSymbolicVariable> equivalenceClassForUpperBound = renamings.get(upperBoundOfRange)
				.get(stateIndex);
		
		if (equivalenceClassForLowerBound.isEmpty() || equivalenceClassForUpperBound.isEmpty())
			return false;
		
		
		LLVMMemoryRange renamedRange = new LLVMMemoryRange(memoryRangeOfFirstState.getFromRef(),
				memoryRangeOfFirstState.getToRef(), memoryRangeOfFirstState.getType(), memoryRangeOfFirstState.getUnsigned());
		renamedRange = renamedRange.replaceReference(renamedRange.getFromRef(),
				equivalenceClassForLowerBound.iterator().next());
		renamedRange = renamedRange.replaceReference(renamedRange.getToRef(),
				equivalenceClassForUpperBound.iterator().next());
		
		if (!((LLVMStoreInstruction) currentInstruction).possiblySharingWith(currentState, renamedRange,aborter))
			return true;
		
		}
		return false;
	}
	
	
	/**
	 * Returns true iff <code>stateIndex</code> is at a function skip edge whose label tells us that it does not affect the current renaming of <code>memoryRangeOfFirstState</code>
	 * 
	 */
	private boolean isHarmlessFunctionSkipEdgeCaseOfUnchanged(LLVMAllocation allocationOfFirstState, LLVMMemoryRange memoryRangeOfFirstState, int stateIndex, LLVMRelationFactory relFactory, Abortion aborter) {
		Node<LLVMAbstractState> currentNode = this.get(stateIndex);
		Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
		LLVMEdgeInformation edgeLabelCurrentToNext = graph.getEdgeObject(currentNode, nextNode);

		
		if(edgeLabelCurrentToNext instanceof LLVMMethodSkipEdge) {
			LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edgeLabelCurrentToNext;
			
			 
			LLVMIntersectionResult intersectionResult = skipEdge.getIntersectionResult();
			//FIXME FEM this is a hotfix
			Set<LLVMMemoryRange> setOfUnchangedMemoryRanges = Collections.emptySet();
			
			Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> renamings = getSymbolicVariableRenamingsOfEachStepIncludingEqualities(relFactory, aborter);
			
			if (!(memoryRangeOfFirstState.getFromRef() instanceof LLVMSymbolicVariable
					&& memoryRangeOfFirstState.getToRef() instanceof LLVMSymbolicVariable))
				throw new IllegalArgumentException("Boundaries of the given range must be symbolic variables");
			
			LLVMSymbolicVariable lowerBoundOfRange = (LLVMSymbolicVariable) memoryRangeOfFirstState.getFromRef();
			LLVMSymbolicVariable upperBoundOfRange = (LLVMSymbolicVariable) memoryRangeOfFirstState.getToRef();
			
			Set<LLVMSymbolicVariable> equivalenceClassForLowerBound = renamings.get(lowerBoundOfRange)
					.get(stateIndex);
			Set<LLVMSymbolicVariable> equivalenceClassForUpperBound = renamings.get(upperBoundOfRange)
					.get(stateIndex);
			
			for(LLVMSymbolicVariable nameOfLowerBound : equivalenceClassForLowerBound) {
				for(LLVMSymbolicVariable nameOfUpperBound : equivalenceClassForUpperBound) {
					LLVMMemoryRange renamedRange =
					    new LLVMMemoryRange(
					        nameOfLowerBound,
					        nameOfUpperBound,
					        memoryRangeOfFirstState.getType(),
					        memoryRangeOfFirstState.getUnsigned()
					    );
					if(setOfUnchangedMemoryRanges.contains(renamedRange)) {
						return true;
					}
				}
			}
		}
		
		
		return false;
	}


	/**
	 * On the path from 0 to <code>indexOfTargetState</code>, is there a state
	 * that contains two different allocations A1, A2, such that A1 is a
	 * renaming of <code>allocationInFirstState</code> and A2 is renamed to
	 * <code>targetAllocation</code>?
	 * 
	 * @param allocationInFirstState
	 * @param indexOfTargetState
	 * @param targetAllocation
	 * @param relFactory
	 * @param aborter
	 * @return
	 */
	private boolean existsStateWithDisjointInitialAndTargetAllocation(LLVMAllocation allocationInFirstState,
			int indexOfTargetState, LLVMAllocation targetAllocation, LLVMRelationFactory relFactory, Abortion aborter) {

		List<LLVMAllocation> renamingsOfFirstStateAllocation = getRenamingsOfAllocation(indexOfTargetState + 1,
				allocationInFirstState, relFactory, aborter);
		for (int stateIndex = 0; stateIndex <= indexOfTargetState; stateIndex++) {
			LLVMAllocation currentRenamingOfAllocationOfFirstState = renamingsOfFirstStateAllocation.get(stateIndex);

			if (currentRenamingOfAllocationOfFirstState == null)
				return false;

			LLVMAbstractState currentState = this.get(stateIndex).getObject();
			List<LLVMAllocation> allAllocationsOfCurrentState = currentState.getAllocations();

			for (LLVMAllocation currentAllocation : allAllocationsOfCurrentState) {
				if (currentAllocation.equals(currentRenamingOfAllocationOfFirstState))
					continue;

				LLVMSEPath pathFromCurrentStateToTargetState = this.subPath(stateIndex, indexOfTargetState + 1);
				List<LLVMAllocation> renamingsOfCurrentAllocationUntilTargetState = pathFromCurrentStateToTargetState
						.getRenamingsOfAllocation(indexOfTargetState + 1 - stateIndex, currentAllocation, relFactory,
								aborter);
				int indexOfAllocationInTargetState = indexOfTargetState - stateIndex;

				if (Globals.useAssertions) {
					assert indexOfAllocationInTargetState == renamingsOfCurrentAllocationUntilTargetState.size() - 1;
				}

				LLVMAllocation renamingOfCurrentAllocationInTargetState = renamingsOfCurrentAllocationUntilTargetState
						.get(indexOfAllocationInTargetState);

				if (renamingOfCurrentAllocationInTargetState != null
						&& renamingOfCurrentAllocationInTargetState.equals(targetAllocation))
					return true;

			}
		}

		return false;
	}

	/**
	 * On the path from 0 to <code>indexOfTargetState</code> (inclusive), is
	 * there a state with a malloc or alloca instruction yielding
	 * <code>targetAllocation</code> in the state denoted by
	 * <code>indexOfTargetState</code>? Furthermore, the <code>allocationInFirstState</code> must not be freed up to that state
	 * 
	 * @param indexOfTargetState
	 * @param targetAllocation
	 *            A malloc allocation of the state whose index on this path is
	 *            <code>indexOfTargetState</code>
	 * @param relFactory
	 * @param aborter
	 * @return
	 */
	private boolean existsAllocatingInstructionResultingInGivenAllocationDisjointFromFirstStateAllocation(LLVMAllocation allocationInFirstState, int indexOfTargetState,
			LLVMAllocation targetAllocation, LLVMRelationFactory relFactory, Abortion aborter) {
		if (!this.get(indexOfTargetState).getObject().getAllocations().contains(targetAllocation))
			throw new IllegalArgumentException(
					"The given target allocation was not part of the allocations of the target state");

		for (int stateIndex = 0; stateIndex < indexOfTargetState; stateIndex++) {
			Node<LLVMAbstractState> currentNode = this.get(stateIndex);
			Node<LLVMAbstractState> nextNode = this.get(stateIndex + 1);
			LLVMEdgeInformation edgeToNextNode = graph.getEdgeObject(currentNode, nextNode);

			LLVMAbstractState currentState = currentNode.getObject();
			LLVMAbstractState nextState = nextNode.getObject();
			LLVMInstruction currentInstruction = currentState.getCurrentInstruction();

			if (edgeToNextNode instanceof LLVMEvaluationInformation) {
				boolean doesMalloc = currentInstruction instanceof LLVMCallInstruction
						&& ((LLVMCallInstruction) currentInstruction).isMallocCall();
				boolean doesAlloca = currentInstruction instanceof LLVMAllocaInstruction;
				if (doesMalloc || doesAlloca) {
					LinkedHashSet<LLVMAllocation> allAllocationsAfterEvaluation = new LinkedHashSet<>(
							nextState.getAllocations());
					allAllocationsAfterEvaluation.removeAll(currentState.getAllocations());

					if (allAllocationsAfterEvaluation.size() != 1)
						throw new IllegalStateException(
								"There should be exactly one allocation left in the list, which is the one that was just allocated");

					LLVMAllocation newlyCreatedAllocation = allAllocationsAfterEvaluation.iterator().next();
					LLVMSEPath pathFromAfterAllocationToTargetState = this.subPath(stateIndex + 1,
							indexOfTargetState + 1);

					ArrayList<LLVMAllocation> renamingsOfNewAllocationFromCreationToTargetState = pathFromAfterAllocationToTargetState
							.getRenamingsOfAllocation(indexOfTargetState - stateIndex, newlyCreatedAllocation,
									relFactory, aborter);
					int indexOfAllocationAtTargetState = indexOfTargetState - stateIndex - 1;

					if (Globals.useAssertions) {
						assert indexOfAllocationAtTargetState == renamingsOfNewAllocationFromCreationToTargetState
								.size() - 1;
					}
					LLVMAllocation renamedNewAllocationInTargetState = renamingsOfNewAllocationFromCreationToTargetState
							.get(indexOfAllocationAtTargetState);

					if (targetAllocation.equals(renamedNewAllocationInTargetState)) {
						//We need to check if the allocation of the first state was not deallocated up to the allocation.
						//Only then we can be sure that the newly allocated memory range is disjoint from the allocation in the first state
						return notDeallocatedUntil(allocationInFirstState, stateIndex, relFactory, aborter).x;
					}
				}
			}

		}

		return false;
	}

	/**
	 * Should work with function skip edges now!
	 * 
	 * @param stopIndexExclusive
	 * @param allocationOfFirstState
	 * @param relFactory
	 * @param aborter
	 * @return List [A_0, A_1, ..., A_l] with l =
	 *         <code>stopIndexExclusive</code> - 1. A_0 is identical to
	 *         <code>allocationOfFirstState</code>, all following A_i are the
	 *         renamings of A_0 along the path from 0 to
	 *         <code>stopIndexExclusive</code>. These A_i may be null if we
	 *         don't know the renaming, probably because the allocation was lost
	 */
	private ArrayList<LLVMAllocation> getRenamingsOfAllocation(int stopIndexExclusive,
			LLVMAllocation allocationOfFirstState, LLVMRelationFactory relFactory, Abortion aborter) {
		if (stopIndexExclusive > this.size())
			throw new IllegalArgumentException("stopIndexExclusive out of range");

		ArrayList<LLVMAllocation> result = new ArrayList<>(stopIndexExclusive);
		Map<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> renamings = getSymbolicVariableRenamingsOfEachStepIncludingEqualities(
				relFactory, aborter);

		if (!(allocationOfFirstState.x instanceof LLVMSymbolicVariable)
				|| !(allocationOfFirstState.y instanceof LLVMSymbolicVariable))
			throw new IllegalStateException("One border is not an LLVMSymbolicVariable");
		LLVMSymbolicVariable lowerBoundInitialAllocation = (LLVMSymbolicVariable) allocationOfFirstState.x;
		LLVMSymbolicVariable upperBoundInitialAllocation = (LLVMSymbolicVariable) allocationOfFirstState.y;

		result.add(allocationOfFirstState);

		boolean lostTrack = false;
		pathLoop: for (int i = 1; i < stopIndexExclusive; i++) {
			LLVMAbstractState currentState = this.get(i).getObject();

			Set<LLVMSymbolicVariable> equivalenceClassForLowerBoundOfAllocation = renamings
					.get(lowerBoundInitialAllocation).get(i);
			Set<LLVMSymbolicVariable> equivalenceClassForUpperBoundOfAllocation = renamings
					.get(upperBoundInitialAllocation).get(i);

			if (equivalenceClassForLowerBoundOfAllocation.isEmpty()
					|| equivalenceClassForUpperBoundOfAllocation.isEmpty() || lostTrack) {
				lostTrack = true;
				result.add(null);
				continue;
			}

			List<LLVMAllocation> allAllocationsOfCurrentState = currentState.getAllocations();

			for (LLVMAllocation currentAllocationOfCurrentState : allAllocationsOfCurrentState) {
				if (!(currentAllocationOfCurrentState.x instanceof LLVMSymbolicVariable)
						|| !(currentAllocationOfCurrentState.y instanceof LLVMSymbolicVariable))
					throw new IllegalStateException("One border is not an LLVMSymbolicVariable");

				LLVMSymbolicVariable lowerBoundCurrentAllocation = (LLVMSymbolicVariable) currentAllocationOfCurrentState.x;
				LLVMSymbolicVariable upperBoundCurrentAllocation = (LLVMSymbolicVariable) currentAllocationOfCurrentState.y;

				if (equivalenceClassForLowerBoundOfAllocation.contains(lowerBoundCurrentAllocation)
						&& equivalenceClassForUpperBoundOfAllocation.contains(upperBoundCurrentAllocation)) {
					result.add(currentAllocationOfCurrentState);
					continue pathLoop;
				}
			}

			result.add(null);
			lostTrack = true;

		}

		if (Globals.useAssertions) {
			assert result.size() == stopIndexExclusive;
			for(int i = 0; i < stopIndexExclusive; i++) {
				LLVMAllocation currentAllocation = result.get(i);
				if(currentAllocation == null) {
					for(int j = i + 1; j < stopIndexExclusive; j++) {
						assert result.get(j) == null: "As soon as we lost track of an allocation (denoted by the renaming being null), all further entries must be null too";
					}
				}
				
			}
		}

		return result;
	}

	// Remark: Works properly with skip edges
	public Map<LLVMAllocation, LLVMAllocation> getRenamingsOfAllocations(LLVMRelationFactory relFactory,
			Abortion aborter) {
		if (renamingsOfAllocationsAlongPath == null) {

			Map<LLVMAllocation, LLVMAllocation> resultMap = new LinkedHashMap<>();

			LLVMAbstractState firstState = getFirst().getObject();
			List<LLVMAllocation> allAllocationsOfFirstState = firstState.getAllocations();
			for (LLVMAllocation currentAllocation : allAllocationsOfFirstState) {
				ArrayList<LLVMAllocation> renamingListOfCurrentAllocation = getRenamingsOfAllocation(size(),
						currentAllocation, relFactory, aborter);
				LLVMAllocation renamingOfCurrentAllocationInLastState = renamingListOfCurrentAllocation.get(size() - 1);

				resultMap.put(currentAllocation, renamingOfCurrentAllocationInLastState);

			}

			renamingsOfAllocationsAlongPath = resultMap;
		}
		return renamingsOfAllocationsAlongPath;
	}

	/**
	 * 
	 * @return #evaluated call instructions on path - #evaluated return
	 *         instructions on path
	 */
	private int calculateStackChangeDifference() {
		int counter = 0;
		int pathLength = this.size() - 1;

		for (int i = 0; i < pathLength; i++) {
			Node<LLVMAbstractState> currentNode = this.get(i);
			Node<LLVMAbstractState> nextNode = this.get(i + 1);
			LLVMEdgeInformation edgeToNextNode = graph.getEdgeObject(currentNode, nextNode);

			if (!(edgeToNextNode instanceof LLVMEvaluationInformation))
				continue;

			LLVMInstruction currentInstruction = currentNode.getObject().getCurrentInstruction();
			if (currentInstruction instanceof LLVMCallInstruction) {
				counter++;
			}
			if (currentInstruction instanceof LLVMRetInstruction) {
				counter--;
			}

		}

		return counter;
	}

	/**
	 * Collect all constraints along the path into one SMT formula
	 * 
	 * @return A formula containing all of the path's constraints
	 */
	public SMTExpression<SBool> toSMTExp() {
		List<SMTExpression<SBool>> clauses = new LinkedList<SMTExpression<SBool>>();
		for (IntegerRelation rel : this.getConstraints()) {
			clauses.add(rel.toSMTExp());
		}
		final LLVMRelationFactory relationFactory = ((LLVMSEGraph)this.graph).getStrategyParameters().SMTsolver.stateFactory
				.getRelationFactory();
		for (ImmutablePair<LLVMAllocation, LLVMAllocation> allocs : this.getAllocationPairs()) {
			clauses.add(LLVMNonterminationProcessor.getDistinctAllocationFormula(allocs.x, allocs.y, relationFactory));
		}
		for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getEdges()) {
			if (edge.getObject() instanceof LLVMMethodSkipEdge) {
				LLVMMethodSkipEdge skipEdge = (LLVMMethodSkipEdge) edge.getObject();
				LLVMSEPath skippedPath = LLVMSEPath
						.backtrackPath((LLVMSEGraph)this.graph, edge.getStartNode(), skipEdge.getEndNode()).iterator().next();
				LLVMProblem.logger.fine("Analysing method skip path " + skippedPath.toString());
				clauses.add(skippedPath.toSMTExp());
			}
		}
		return Core.and(clauses);
	}

	public LLVMSEPath subPath(int fromIndex, int toIndex) {
		List<Node<LLVMAbstractState>> subList = super.subList(fromIndex, toIndex);
		LLVMSEPath resultPath = new LLVMSEPath(subList, graph);

		if(fromIndex == 0) {
			resultPath.renamingsClassesAlongPath = new LinkedHashMap<>();
			for(Map.Entry<LLVMSymbolicVariable, ArrayList<Set<LLVMSymbolicVariable>>> entry : this.renamingsClassesAlongPath.entrySet()) {
				resultPath.renamingsClassesAlongPath.put(entry.getKey(), new ArrayList<>( entry.getValue().subList(fromIndex, toIndex)));
			}
		}
		
		// TODO: We could reuse more of the renamings to improve performance

		return resultPath;
	}

	@Override
	public String toString() {
		List<Integer> nodeNumbers = new LinkedList<>();
		for (Node<LLVMAbstractState> node : this) {
			nodeNumbers.add(Integer.valueOf(node.getNodeNumber()));
		}
		return nodeNumbers.toString();
	}

	public Node<LLVMAbstractState> getFirst() {
		return get(0);
	}

	public Node<LLVMAbstractState> getLast() {
		return get(size() - 1);
	}
	
	public SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> getGraph() {
		return graph;
	}
	
	public boolean isCyclic() {
		return size() > 2 && get(0) == get(size()-1);
	}

}
