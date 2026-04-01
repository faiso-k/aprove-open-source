package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
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
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class LLVMStandardStep extends LLVMAbstractGraphConstructionStep {

	private final Node<LLVMAbstractState> curNode;
	
	LLVMStandardStep(LLVMSEGraph graph, Node<LLVMAbstractState> node) {
		super(graph);
		this.curNode = node;
		
		if(Globals.useAssertions) {
			assert !isObsolete() : "Step was obsolete immediately after its creation!";
		}
	}

	
	@Override
	public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug) throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
		if(Globals.useAssertions) {
			assert graph.contains(curNode);
		}
		if(Globals.useAssertions) {
			assert graph.getOut(curNode).isEmpty() : 
				"GRAPH CONSISTENCY ERROR: Node already had successor when we wanted to evaluate it furhter";
		}
		
		LLVMAbstractState curState = curNode.getObject();
		int nodeNumber = curNode.getNodeNumber();
		
		List<LLVMAbstractGraphConstructionStep> newSteps = Collections.emptyList();
		
		boolean partOfFunctionGraph = getIntersectionHeuristics().bottomMostFunctionIntersectable(curState);
		
		//If we summarize a function, all nodes part of that function (or called from it) must prove memory safey
		boolean proveMemorySafety = graph.getStrategyParameters().proveMemorySafety;// || partOfFunctionGraph;
		
		LLVMMemoryChangeTracker tracker = null;
		boolean removeNonLiveVariables = false;
		if(partOfFunctionGraph) {
			LLVMFunctionGraph fg = graph.getFunctionGraphTracker().getFunctionGraph(curState.getBottommostFunctionInStack());
			tracker = fg.getMemoryChangeTracker();
			removeNonLiveVariables = getIntersectionHeuristics().shouldRemoveNonLiveVariablesFromStatesEvaluationResult(curState);
		}
		
		Set<LLVMSymbolicEvaluationResult> evaluations = curState.evaluate(nodeNumber, proveMemorySafety, removeNonLiveVariables, tracker, aborter);
        if (evaluations == null) return Collections.emptyList();
        if (evaluations.size() == 1) {
            // no refinement was performed
            // TODO: remove this
            if (debug) {
                System.err.println("Evaluate");
            }
            // evaluate
            LLVMSymbolicEvaluationResult evaluation = evaluations.iterator().next();
            LLVMAbstractState newState;
            if (evaluation != null) {
                newState = evaluation.x;
            } else {
                newState = null;
            }
            // is there a successor state?
            if (newState != null) {
                // add the successor state
            	newState = handleVarToEntryStateMapForEvaluationOrRefinement(newState,true);
                Node<LLVMAbstractState> newNode = new Node<LLVMAbstractState>(newState);
                graph.addEdge(curNode, newNode, new LLVMEvaluationInformation(evaluation.y));
                
                newSteps = checkInvariantsAndAttemptGeneralization(newNode, aborter);
            }
            if (debug) {
                System.err.println("New State: " + newState);
            }
        } else {
            if (debug) {
                System.err.println("Refinement");
            }
            // refinement was needed => new states
            // add edges to new state nodes and nodes to the stack
            newSteps = new ArrayList<>();
            for (LLVMSymbolicEvaluationResult refinement : evaluations) {
            	LLVMAbstractState newState = handleVarToEntryStateMapForEvaluationOrRefinement(refinement.getState(),false);
                Node<LLVMAbstractState> newNode = new Node<LLVMAbstractState>(newState);
                graph.addEdge(curNode, newNode, new LLVMRefinementInformation(refinement.getStateChangeInfo()));
                newSteps.addAll(checkInvariantsAndAttemptGeneralization(newNode, aborter));
                if (debug) {
                    System.err.println("New State: " + newNode.getObject());
                }
            }
        }
        
        return newSteps;
	}
	
    private boolean mustNotGeneralize(Node<LLVMAbstractState> generalizationCandidate, Abortion aborter) {
    	
    	
    	LLVMAbstractState generalizationCandidateState = generalizationCandidate.getObject();
    	LLVMProgramPosition pos = generalizationCandidateState.getProgramPosition();
    	boolean result = generalizationCandidateState.isRefined();
    	
    	if (generalizationCandidateState.isErrorState() || generalizationCandidateState.isInconsistentState() || getIntersectionHeuristics().isReturnState(generalizationCandidateState)
    			|| getIntersectionHeuristics().isCallState(generalizationCandidateState)) {
    	    return true;
    	}
    	result |= !pos.isFirstNonPhiInstruction(getModule()) 
    			&& !(getIntersectionHeuristics().isIntersectedState(curNode.getObject()) && getIntersectionHeuristics().canMergeEvaluationOfIntersectedState(curNode.getObject()));
        result |= generalizationCandidateState.satisfiesReturnConditions(aborter).x;
        
        for(Edge<LLVMEdgeInformation,LLVMAbstractState> edge : graph.getInEdges(generalizationCandidate)) {
        	if(edge.getObject() instanceof LLVMMethodSkipEdge)
        		return true;
        }
        
        return result;
    }
    

	
    /**
     * Adds a node to the index blockToNode and also checks if a
     * generalization is possible. If this node is an instance of another node
     * a generalization edge will be added. If there is another node with the
     * same position (which is the first within a basic block) and refinement state, which is not a generalization
     * of this node, then it will be tried to create a new generalized node of
     * both nodes.
     * @param newNode The node to add.
     * @return A node that should be evaluated later. May be newNode itself, a generalization of newNode or null if
     * no further evaluation is necessary (in case it was an instance of another state)
     * @throws UndefinedBehaviorException
     * @throws MemorySafetyException
     * @throws MemoryLeakException If information about mallocated memory gets lost.
     */
    Node<LLVMAbstractState> addNodeToPCListAndGeneralize(Node<LLVMAbstractState> newNode, Abortion aborter)
    throws MemorySafetyException, UndefinedBehaviorException, MemoryLeakException {
        if (Globals.useAssertions) {
            assert (newNode != null);
        }
        LLVMAbstractState newState = newNode.getObject();
        LLVMProgramPosition pos = newState.getProgramPosition();
        /*
         * If one of these conditions holds, we never want it in our list:
         * - it is a refined or error state
         * - its position is not the first one in a block
         * - its return conditions are satisfied
         */
        // TODO can we use possible updates here?
        if (mustNotGeneralize(newNode, aborter)) {
            return newNode;
        }
        
        //Does the state look like one where we need fast convergence of the graph construction,
        //e.g. due to many conditional branches?
        LLVMForceMergeHeuristic forceMergeHeuristics = graph.getForceMergeHeurisics();
        boolean needFastConvergence = forceMergeHeuristics.needFastConvergenceForState(newState);
        
        ImmutablePair<String, String> block = new ImmutablePair<String, String>(pos.getFunction(), pos.getBlock());
        // determine nodes at the beginning of the same block
        List<Node<LLVMAbstractState>> nodesAtSameBlock = graph.getBlockToNode().get(block);
        // No related states: Nothing to do, so just add it to the list and go away.
        if (nodesAtSameBlock == null) {
        	//if not in fast convergence mode, we do not add the node to the list 
        	//this means we will not merge with program positions when encountering them for the first time
            nodesAtSameBlock = new LinkedList<Node<LLVMAbstractState>>(needFastConvergence ? Collections.singleton(newNode) : Collections.emptySet());
            graph.getBlockToNode().put(block, nodesAtSameBlock);
            return newNode;
        }
        // else we have seen this position before
        Map<LLVMAbstractState, Node<LLVMAbstractState>> stateToNodeMap =
            new LinkedHashMap<LLVMAbstractState, Node<LLVMAbstractState>>();
        
        for (Node<LLVMAbstractState> node : nodesAtSameBlock) {
            aborter.checkAbortion();
            // These are not interesting here:
            LLVMAbstractState otherState = node.getObject();
            if (newState.getCallStack().size() != otherState.getCallStack().size()) {
                continue;
            }
            stateToNodeMap.put(otherState, node);
        }
        
        Pair<Boolean,Boolean> heuristicMergingAnswer = forceMergeHeuristics.haveToGeneralize(graph,newNode, new ArrayList<Node<LLVMAbstractState>>(stateToNodeMap.values()),aborter);
        boolean haveToGeneralize = heuristicMergingAnswer.x;
        boolean agressiveMergeNeeded = heuristicMergingAnswer.y;
        
        final LLVMRelationFactory relationFactory =
            this.getStrategyParameters().SMTsolver.stateFactory.getRelationFactory();
        final LLVMMergeResult genRes;
        if (haveToGeneralize) {
        	LLVMAbstractState weakened = null;
        	if(!agressiveMergeNeeded) {
        		weakened = newState.generalizeWithoutMerging();
        	}
            if (weakened != null) {
                LLVMProgramPosition newPos = newState.getProgramPosition();
                ImmutablePair<String, String> newBlock = new ImmutablePair<String, String>(newPos.getFunction(), newPos.getBlock());
                if (graph.getBlockToNode().containsKey(newBlock)) {
                	graph.getBlockToNode().get(newBlock).remove(newNode);
                }
                graph.markNodeUnneeded(newNode);
                Node<LLVMAbstractState> generalizedNode = new Node<LLVMAbstractState>(weakened);
                Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap = new LinkedHashMap<LLVMSimpleTerm, LLVMSimpleTerm>();
                for (LLVMSymbolicVariable ref : weakened.getSymbolicVariables()) {
                    refMap.put(ref, ref);
                }
                graph.addEdge(
                    newNode,
                    generalizedNode,
                    new LLVMGeneralizationInformation(newNode, Collections.emptySet(), refMap)
                );
                nodesAtSameBlock.add(generalizedNode);
                return generalizedNode;
            } else {
                genRes = this.getStrategyParameters().SMTsolver.stateFactory.merge(newState, stateToNodeMap.keySet(), agressiveMergeNeeded, needFastConvergence, aborter);
            }
        } else {
            genRes =
                this.getStrategyParameters().SMTsolver.stateFactory.searchBestInstance(
                    newState,
                    stateToNodeMap.keySet(),
                    aborter
                );
        }
        if (!(genRes.getTotalCost() < java.lang.Double.POSITIVE_INFINITY)) {
            // Merging failed.
        	if(agressiveMergeNeeded) {
        		throw new IllegalStateException("We really should have merged, but couldn't");
        	}
            nodesAtSameBlock.add(newNode);
            return newNode;
        }
        LLVMAbstractState partnerState = genRes.getOlderState();
        Node<LLVMAbstractState> partnerNode = stateToNodeMap.get(partnerState);
        // If this is an instance, we just need an edge and are done:
        if (genRes.isInstance()) {
            final Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap =
                LLVMSEGraph.getRefCorrespondenceMap(newState, partnerState, genRes.getAllocationBijection());
            final Set<LLVMRelation> changes = newState.getInvariants();
            graph.addEdge(newNode, partnerNode, new LLVMInstantiationInformation(changes, refMap));
            return null;
        }
        // We have a merge/generalization. First, find the part of the graph that will now be redone in a more general
        // manner:
        // Here, we respect that the intersection heuristics may tell us to keep certain function executions for later reuse
        Collection<Node<LLVMAbstractState>> nowUnneededNodes = 
        		graph.findUnneededNodes(Collections.singleton(partnerNode),Collections.emptySet(),conditionallyStopAtEntryNodes,aborter); 
        
        
        for(Node<LLVMAbstractState> unneeded : nowUnneededNodes) {
        	LLVMAbstractState unneededState = unneeded.getObject();
        	if(getIntersectionHeuristics().isCallAbstractionOrEntryState(unneededState)) {
        		System.err.println("deleted entry node of " + unneededState.getCurrentFunction());
        	}
        	
        	if(unneededState.getProgramPosition().toString().equals("(test, 1, 0)")) {
        		System.err.println("Deleted loop header of test!");
        	}
        	
        } 
        
        final boolean newNodeNeeded = !nowUnneededNodes.contains(newNode);
        // Remove it from our internal structures:
        for (Node<LLVMAbstractState> unnededNode : nowUnneededNodes) {
            graph.markNodeUnneeded(unnededNode);
        }
        // Add new node to the graph:
        LLVMSymbolicEvaluationResult post = genRes.getGeneralizedState().postProcessAfterGeneralization(false, aborter);
        Node<LLVMAbstractState> generalizedNode = new Node<LLVMAbstractState>(post.getState());
        final Map<LLVMSimpleTerm, LLVMSimpleTerm> newRefMap =
            LLVMSEGraph.getRefCorrespondenceMap(newState, post.getState(), genRes.getAllocationBijection(false));
        final Map<LLVMSimpleTerm, LLVMSimpleTerm> partnerRefMap =
            LLVMSEGraph.getRefCorrespondenceMap(
                partnerState,
                post.getState(),
                genRes.getAllocationBijection(true)
            );
        /*
         * If we remove the unneeded nodes (except for partnerNode) from the graph, we need an edge from partnerNode to
         * generalizedNode and information about newNode (which is removed, since it is contained in unneededNodes).
         * Otherwise we just add an edge from newNode to generalizedNode with information about partnerNode.
         */
        if (LLVMDebuggingFlags.REMOVE_TOO_CONCRETE_PARTS_FROM_GRAPH) {
            for (Node<LLVMAbstractState> node : nowUnneededNodes) {
                if (!node.equals(partnerNode)) {
                    graph.removeNode(node);
                }
            }
            graph.addEdge(
                partnerNode,
                generalizedNode,
                new LLVMGeneralizationInformation(newNode, post.getStateChangeInfo(), partnerRefMap)
            );
            if (newNodeNeeded) {
            	graph.addEdge(
                    newNode,
                    generalizedNode,
                    new LLVMGeneralizationInformation(partnerNode, post.getStateChangeInfo(), newRefMap)
                );
            }
        } else {
        	graph.addEdge(
                newNode,
                generalizedNode,
                new LLVMGeneralizationInformation(partnerNode, post.getStateChangeInfo(), newRefMap)
            );
        	graph.addEdge(
                partnerNode,
                generalizedNode,
                new LLVMGeneralizationInformation(newNode, post.getStateChangeInfo(), partnerRefMap)
            );
        }
        nodesAtSameBlock.add(generalizedNode);
        return generalizedNode;
    }
	
	/**
     * Adds a node to the end of the list of the unevaluated nodes and
     * generalizes this node if possible.
     * @param node The node to add.
     * @throws MemorySafetyException If a memory safety violation occurred.
     * @throws UndefinedBehaviorException
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException TODO:???
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    List<LLVMAbstractGraphConstructionStep> checkInvariantsAndAttemptGeneralization(Node<LLVMAbstractState> node, Abortion aborter)
    throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {
        LLVMAbstractState state = node.getObject();
        if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS && state instanceof LLVMHeuristicState) {
            LLVMHeuristicState heuristicState = (LLVMHeuristicState)state;
            assert (heuristicState.isClean() && heuristicState.isAdjusted()) :
                "State in graph has not been cleaned and adjusted!";
            for (LLVMHeuristicRelation rel : heuristicState.getRelations()) {
                assert (!rel.isSimpleEquation()) :
                    "Found simple equation in node (" + node.getNodeNumber() + ")!";
                assert (
                    !(rel.getLhs() instanceof LLVMHeuristicConstRef && rel.getRhs() instanceof LLVMHeuristicConstRef)
                ) :
                    "We should not have relations over constants in a state (node "
                    + node.getNodeNumber()
                    + ")!";
            }
            for (Map.Entry<LLVMHeuristicVariable, LLVMValue> entry : heuristicState.getValues().entrySet()) {
                if (entry.getValue().isIntLiteral()) {
                    assert (heuristicState.isPossiblyTrapValue(entry.getKey())) :
                        "Constant value in node ("
                        + node.getNodeNumber()
                        + ")!";
                }
            }
        }
        if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
            LLVMTermFactory termFactory = this.getStrategyParameters().SMTsolver.stateFactory.getRelationFactory().getTermFactory();
            if (state.checkRelation(termFactory.zero(), IntegerRelationType.NE, termFactory.zero(),aborter).x) {
                throw new IllegalStateException("False state!");
            }
        }
        

            final Node<LLVMAbstractState> nodeToAdd = this.addNodeToPCListAndGeneralize(node, aborter);

            return createConstructionStepForUnevaluatedNode(nodeToAdd);
        
    }

	@Override
	public boolean isObsolete() {
		return !graph.contains(curNode) || graph.isNodeUnneeded(curNode);
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((curNode == null) ? 0 : curNode.hashCode());
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
		final LLVMStandardStep other = (LLVMStandardStep) obj;
		if (this.graph != other.graph) {
			return false;
		}

		if (this.curNode != other.curNode) {
			return false;
		}


		return true;
	}
	
	EdgeFilter<LLVMEdgeInformation,LLVMAbstractState> conditionallyStopAtEntryNodes = new EdgeFilter<LLVMEdgeInformation,LLVMAbstractState>() {

		//We may deliberately stop the search for unneeded nodes after generalization at entry nodes of intersectable functions
		//if the intersection heuristics tell us to. This would mean that we keep the graph representing the called function for possible later reuse
		
		@Override
		public boolean selectEdge(Node<LLVMAbstractState> source, Node<LLVMAbstractState> dest,
				LLVMEdgeInformation label) {
			if((label instanceof LLVMCallAbstractionEdge || label instanceof LLVMInstantiationInformation) && dest.getObject().getCallStack().isEmpty()) {
				LLVMAbstractState destState = dest.getObject();
				String function = destState.getCurrentFunction();
				if(getIntersectionHeuristics().isIntersectableFunction(function)) {
					if(graph.getFunctionGraphTracker().getFunctionGraph(function).getNonGeneralizedEntryNodes().contains(dest)) {
						
						//selecting an edge here means that the successors of the dest node are considered for removing
						return !getIntersectionHeuristics().keepSubGraphsForFunctionWhenRemovingUnneededNodesAferGeneralization(destState);
					}
				}
				
				
			}
			return true;
		}

	};
	

	
	private LLVMAbstractState handleVarToEntryStateMapForEvaluationOrRefinement(LLVMAbstractState newState, boolean isEvaluation) {
		if(curNode.getObject().getEntryStateVarCorrespondenceMap() == null) {
			
			//disabled, no change needed
			return newState;
		}
		
		LLVMFunctionGraph fg = graph.getFunctionGraphTracker().getFunctionGraph(newState.getBottommostFunctionInStack());
		LLVMModule module = graph.getModule();
		
		return LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.handleVarToEntryStateMapForEvaluationOrRefinement(fg, module, curNode, newState, isEvaluation);
	}
    



}
