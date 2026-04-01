package aprove.input.Programs.llvm.internalStructures.intersecting;

import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.MergingStrategies.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.relationeval.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.static_analysis.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Contains methods to make decisions about intersections.
 * For example, which functions should be intersected in addition to recursive functions (which are always intersected)
 * @author Frank Emrich
 *
 */
//TODO: allow changing opinion on non-recursive functions as long as they are not in the graph? E.g., at first state containing them?
	//Once they are stateful, it may become a problem to just share them in the immutable function graphs
public class LLVMIntersectionHeuristics {

	private final static int INSTRUCTION_COUNT_THRESHOLD_TO_ACTIVATE_SUMMARIZATION = Globals.INSTRUCTION_COUNT_THRESHOLD;
	private final static int UNCOND_BRANCH_COUNT_OF_FUNCTION_TO_INTERSECT = 4; 
	private final static boolean INTERSECT_FUNCTIONS_WITH_LOOP = true;
	private final static boolean INTERSECT_ALL_FUNCTIONS_CALLED_FROM_LOOP = true;
	private final static int INTERSECT_FUNCTIONS_CALLED_FROM_AT_LEAST_N_DIFFERENT_POSITIONS = 2;
	private final static boolean INTERSECT_FUNCTIONS_CALLING_OTHER_FUNCTIONS = true;
	private final static boolean INTERSECT_FUNCTIONS_IN_CALL_REACHABILITY_CLOSURE = false;
	
	
	
	
	public static class IntersectionSettings {
		EntryStateMergingStrategy entryStateMeringStrategy;
		boolean searchEntryStateInstanceIfMergingNotEnfored;
		boolean onlyUseEntryStateInstanceIfSameNumberOfAllocations;
		
		
		ReturnStateMergingStrategy returnStateMergingStrategy;
		boolean searchReturnStateInstanceIfMergingNotEnfored;
		boolean onlyUseReturnStateInstanceIfSameNumberOfAllocations;
	}
	

	
	private IntersectionSettings settingsForRecursiveFunctions = new IntersectionSettings();
	
	
	private IntersectionSettings settingsForNonRecursiveFunctions = new IntersectionSettings();
	
	private void setupSettings() {
		//recursive functions
		settingsForRecursiveFunctions.entryStateMeringStrategy = 
				EntryStateMergingStrategy.ENFORCE_SINGLE_ENTRY_STATE_PER_FUNCTION;
		settingsForRecursiveFunctions.searchEntryStateInstanceIfMergingNotEnfored = true;
		settingsForRecursiveFunctions.onlyUseEntryStateInstanceIfSameNumberOfAllocations = false;
		
		settingsForRecursiveFunctions.returnStateMergingStrategy =
				ReturnStateMergingStrategy.MERGE_IF_AT_SAME_PROGPOS_AND_HAVE_SAME_PROGRAVS;
		settingsForRecursiveFunctions.searchReturnStateInstanceIfMergingNotEnfored = true;
		settingsForRecursiveFunctions.onlyUseReturnStateInstanceIfSameNumberOfAllocations = false;
		
		
		//non-recursive functions
		settingsForNonRecursiveFunctions.entryStateMeringStrategy = 
				EntryStateMergingStrategy.ENFORCE_SINGLE_ENTRY_STATE_PER_FUNCTION;
		settingsForNonRecursiveFunctions.searchEntryStateInstanceIfMergingNotEnfored = true;
		settingsForNonRecursiveFunctions.onlyUseEntryStateInstanceIfSameNumberOfAllocations = false;
		
		settingsForNonRecursiveFunctions.returnStateMergingStrategy =
				ReturnStateMergingStrategy.MERGE_IF_AT_SAME_PROGPOS_AND_HAVE_SAME_PROGRAVS;
		settingsForNonRecursiveFunctions.searchReturnStateInstanceIfMergingNotEnfored = true;
		settingsForNonRecursiveFunctions.onlyUseReturnStateInstanceIfSameNumberOfAllocations = false;
		
	}

	
	private final LLVMModule module;

	private final Abortion aborter;

	private final LLVMParameters parameters;

	private LLVMCallGraph callGraph;
	
	//Names of functions (without @) that we determined to be recursive
	private Set<String> recursiveFunctions;
	
	//Names of functions (without @), that are NOT recursive,
	//but we still want to do intersect them.
	private Set<String> nonRecursiveIntersectableFunctions;
	

	
	public LLVMIntersectionHeuristics(LLVMModule module, LLVMParameters parameters, Abortion aborter) {
		this.module = module;
		this.aborter = aborter;
		this.parameters = parameters;
		this.callGraph = new LLVMCallGraph(module);
		this.recursiveFunctions = callGraph.getRecursiveFunctions();
		this.nonRecursiveIntersectableFunctions = intersectionHeuristic();
		
		setupSettings();
	}
	
	
	//right now set to treat all functions as intersectable, for debugging
	//TODO FEM: what about the root function?
	//TODO make sure that there are no functions in here that immediatly return, i.e., entry states and return states are disjoint
	/**
	 * This is a heuristic that decides which non-recursive function should be intersected in the graph
	 */
	private Set<String> intersectionHeuristic() {
		Set<String> intersectableNonRecursive = new LinkedHashSet<>();
		if(Globals.useAssertions && Globals.DEBUG_FEMRICH) {
			assert intersectableNonRecursive.stream().allMatch(name -> !name.startsWith("@"));
		}
		
		int instructionCount = module.getAllPositions().size();
		
		if(instructionCount > INSTRUCTION_COUNT_THRESHOLD_TO_ACTIVATE_SUMMARIZATION) {
			System.err.println("Instruction count:" + module.getAllPositions().size());
			
			LLVMControlFlowGraphIntraFunctional cfg = new LLVMControlFlowGraphIntraFunctional(module);
			LLVMFunctionInstructionCounter instrCounter = new LLVMFunctionInstructionCounter(module);
			
			
			Set<String> allFunctions = module.getFunctions().keySet();
			
			for(String function : allFunctions) {
				if(INTERSECT_FUNCTIONS_WITH_LOOP && cfg.functionContainsLoop(function)) {
					intersectableNonRecursive.add(function);
				}
				
				if(INTERSECT_ALL_FUNCTIONS_CALLED_FROM_LOOP && cfg.functionIsCalledFromLoop(function)) {
					intersectableNonRecursive.add(function);
				}
				
				int conditionalBranchCount = instrCounter.getNumberOfInstructionsOfFunctionAndType(function, LLVMCondBrInstruction.class);
				if(conditionalBranchCount > UNCOND_BRANCH_COUNT_OF_FUNCTION_TO_INTERSECT) {
					intersectableNonRecursive.add(function);
				}
				
				int distinctProgramPositionsFunctionIsCalledFrom = instrCounter.getNumberOfCallsOfFunction(function);
				if(distinctProgramPositionsFunctionIsCalledFrom > INTERSECT_FUNCTIONS_CALLED_FROM_AT_LEAST_N_DIFFERENT_POSITIONS) {
					intersectableNonRecursive.add(function);
				}
				
				if(INTERSECT_FUNCTIONS_CALLING_OTHER_FUNCTIONS && !callGraph.functionsCalledBy(function).isEmpty() ) {
					intersectableNonRecursive.add(function);
				}
			}

			
		}
		Set<String> reachabilityClosure = new LinkedHashSet<>();
		if(INTERSECT_FUNCTIONS_IN_CALL_REACHABILITY_CLOSURE) {
			for(String function : intersectableNonRecursive) {
				reachabilityClosure.addAll(callGraph.functionsCalledByTransitive(function));
			}
		}
		intersectableNonRecursive.addAll(reachabilityClosure);
		
		//Manual set especially for email_spec0_product05_true-unreach-call_true-termination
		/*intersectableNonRecursive.clear();
		intersectableNonRecursive.addAll(Arrays.asList(new String[] {
				"f",
				"g"}));
		*/
		/*intersectableNonRecursive.addAll(Arrays.asList(new String[] {
				"test",
				"select_one",
				"createEmail",
				"printMail",
				"forward",
				"sendEmail",
				"createClient",
				"incoming",
				"incoming__wrappee__Base",
				"outgoing",
				"mail",
				"setClientId",
				"getClientId",
				"setClientForwardReceiver",
				"getClientForwardReceiver",
				"setClientKeyringPublicKey",
				"findPublicKey",
				"getClientKeyringPublicKey",
				"setClientKeyringUser",
				"getClientKeyringUser",
				"createClientKeyringEntry",
				"setClientKeyringSize",
				"getClientKeyringSize",
				"setClientPrivateKey",
				"getClientPrivateKey",
				"setClientAutoResponse",
				"getClientAutoResponse",
				"setClientAddressBookAddress",
				"getClientAddressBookAddress",
				"setClientAddressBookAlias",
				"findClientAddressBookAlias",
				"getClientAddressBookAlias",
				"createClientAddressBookEntry",
				"setClientAddressBookSize",
				"getClientAddressBookSize",
				"setClientOutbuffer",
				"getClientOutbuffer",
				"setClientName",
				"getClientName",
				"initClient", //just one branching 
				"isReadable", //just one branching 
				"__utac__get_this_argtype",
				"__utac__get_this_arg",
				
		}));*/
		
		intersectableNonRecursive.removeAll(recursiveFunctions);
		
		//remove functions which immediately return
		Iterator<String> candidateIt = intersectableNonRecursive.iterator();
		while (candidateIt.hasNext()) {
			String candidateFunction = candidateIt.next();
			LLVMFnDeclaration fnDecl = module.getFunctions().get(candidateFunction);
			if (!(fnDecl instanceof LLVMFnDefinition)) {
				candidateIt.remove();
			} else {
				LLVMFnDefinition actFunction = (LLVMFnDefinition) fnDecl;
				LLVMProgramPosition initialProgPos = new LLVMProgramPosition(candidateFunction,
						actFunction.getNameOfFirstBlock(), 0);
				LLVMInstruction initialInstr = module.getInstruction(initialProgPos);
				if (initialInstr instanceof LLVMRetInstruction) {
					candidateIt.remove();
				}
			}
		}
		
		
		return intersectableNonRecursive;
	}

	
	/**
	 * For a given call state, create the call abstraction (i.e., cut off all put the topmost stack frame).
	 * Then, we remove "unreachable" components of the state (e.g., allocations which we cannot possibly access)
	 */
    public LLVMAbstractState createSimplifiedCallAbstraction(LLVMAbstractState callState, Abortion aborter) {
    	String function = callState.getCurrentFunction();
    	//heuristic states have restrictToUsedReferences, thus we do not have to do any further simplification
		//unless we want to support non heuristic states
		//TODO
    	boolean shouldRemoveNonLiveVariables = !(recursiveFunctions.contains(function));
    	LLVMAbstractState callAbstraction = callState.getCallStackAbstractedState(shouldRemoveNonLiveVariables,getAborter());
    	
    	
    	if(recursiveFunctions.contains(function)) {
    		
    	} else {
    		if(callAbstraction instanceof LLVMHeuristicState) {
    			LLVMHeuristicState heuristicCallAbstraction  = (LLVMHeuristicState) callAbstraction;
    			heuristicCallAbstraction = heuristicCallAbstraction.retainReachableAllocationsAndHeapInfo(getAborter());
    			heuristicCallAbstraction = heuristicCallAbstraction.restrictToUsedReferences(null, aborter);
    			//todo live variable analysis here once we do not use it globally any more
    			
    			callAbstraction = heuristicCallAbstraction;
    		}
    	}
    	
    	if(trackVariableRenamingsInStateForFunction(function)) {
    		callAbstraction = LLVMStateBasedSymbolicVariableRenamingRelationEvaluator.initEntryStateVarMapForEntryState(callAbstraction);
    	}
    	if(trackAllocationModificationInStateForFunction(function)) {
    		callAbstraction = LLVMStateBasedAllocationDeallocationEvaluator.initializeMapForEntryState(callAbstraction);
    	}
    	
    	return callAbstraction;
    }
    

    
    
	// return null if we didn't find an instance and don't have to merge
	// the second component is the node of the merge partner (merge case)/ the
	// generalization (instance case)
	public Pair<LLVMMergeResult, Node<LLVMAbstractState>> searchGeneralizationOrMergeCallAbstraction(
			Node<LLVMAbstractState> callAbstraction, Node<LLVMAbstractState> callNode,
			LLVMSEGraph seGraph,LLVMFunctionGraph fg) throws MemoryLeakException {
		String function = callAbstraction.getObject().getCurrentFunction();
		if(recursiveFunctions.contains(function)) {
			return searchGeneralizationOrMergeCallAbstraction(callAbstraction,callNode, settingsForRecursiveFunctions,seGraph,fg);
		} else {
			return searchGeneralizationOrMergeCallAbstraction(callAbstraction,callNode, settingsForNonRecursiveFunctions,seGraph,fg);
		}
	}

	private Pair<LLVMMergeResult, Node<LLVMAbstractState>> searchGeneralizationOrMergeCallAbstraction(
			Node<LLVMAbstractState> callAbstraction, Node<LLVMAbstractState> callNode, IntersectionSettings settings,
			LLVMSEGraph seGraph, LLVMFunctionGraph fg) throws MemoryLeakException {
		String function = callAbstraction.getObject().getCurrentFunction();
		LLVMAbstractState callAbstractionState = callAbstraction.getObject();
		//SimpleGraph<LLVMAbstractState,LLVMEdgeInformation> seGraph = fg.getGraph();
		
		Set<Node<LLVMAbstractState>> nonGeneralizedEntryNodes = fg.getNonGeneralizedEntryNodes();
		Set<Node<LLVMAbstractState>> callNodes = fg.getCallNodes();
		Map<LLVMAbstractState, Node<LLVMAbstractState>> entryStatesToEntryNodes = new LinkedHashMap<>();
		for(Node<LLVMAbstractState> nonGeneralizedEntryNode : nonGeneralizedEntryNodes) {
			entryStatesToEntryNodes.put(nonGeneralizedEntryNode.getObject(),nonGeneralizedEntryNode);
		}
		
		
		Set<Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>>> existingCallNodeEntryNodePairs =
				new LinkedHashSet<>();
		
	
		for (Node<LLVMAbstractState> otherCallNode : callNodes) {
			Node<LLVMAbstractState> otherCallAbstraction = fg.getCallAbstraction(otherCallNode);
			
			if(otherCallAbstraction == null)
				continue; //Call node was not evaluated further so far
			
			Node<LLVMAbstractState> otherMostGeneralEntryNode = fg.getMostGeneralEntryNode(otherCallAbstraction);
			
			if (otherCallNode == callNode || otherMostGeneralEntryNode == callAbstraction)
				continue;
			
			Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> newPair = new Pair<>(otherCallNode,otherMostGeneralEntryNode);
			existingCallNodeEntryNodePairs.add(newPair);
		}
		
		
		
		//Add those entry nodes which aren't reachable via a call node
		//for example, a root node
		Set<Node<LLVMAbstractState>> alsoNeedToAdd = new LinkedHashSet<>(nonGeneralizedEntryNodes);
		alsoNeedToAdd.removeIf(
				en -> existingCallNodeEntryNodePairs.stream().anyMatch(p -> p.y == en));
		for(Node<LLVMAbstractState> entryNode : alsoNeedToAdd) {
			if(entryNode != callAbstraction) {
				existingCallNodeEntryNodePairs.add(new Pair<>(null,entryNode));
			}
			
		}
		
		//We remove those pairs where the second component (i.e., the call abstraction/entry state)
		//currently has a corresponding construction step in the queue (i.e., it will be treated on its own later)
		existingCallNodeEntryNodePairs.removeIf(pair -> seGraph.anyGraphConstructionStepInQueueMatchesPredicate(isStepForCallAbstraction(pair.y)));
		
		//We ask the settings which entry nodes we have to merge with (possibly none)
		Set<Node<LLVMAbstractState>> entryNodesToMergeWith = 
				settings.entryStateMeringStrategy.mustMergeWith(fg, callNode, callAbstraction, existingCallNodeEntryNodePairs);
		Set<LLVMAbstractState> entryStatesToMergeWith = entryNodesToMergeWith
				.stream()
				.map(n -> n.getObject())
				.collect(Collectors.toCollection(LinkedHashSet::new));
		
		if (!entryStatesToMergeWith.isEmpty()) {
			//We have found older entry states which we must merge with

			LLVMMergeResult mergeRes = getLLVmParameters().SMTsolver.stateFactory.merge(callAbstractionState, entryStatesToMergeWith,
					true, false, getAborter());
			if (mergeRes.getGeneralizedState() == null) {
				throw new IllegalStateException("Was supposed to merge entry nodes but failed");
			}

			return new Pair<>(mergeRes, entryStatesToEntryNodes.get(mergeRes.getOlderState()));
		}
		


		// If we come here, we didn't find have to merge
		// If the strategy tells us to, we look if we can still find a
		// generalization (without merging)
		if (settings.searchEntryStateInstanceIfMergingNotEnfored) {
			Set<LLVMAbstractState> entryStatesToSearchInstanceIn = new LinkedHashSet<>();
			for (Node<LLVMAbstractState> nonGeneralizedEntryNode : fg.getNonGeneralizedEntryNodes()) {
				LLVMAbstractState state = nonGeneralizedEntryNode.getObject();
				if (nonGeneralizedEntryNode != callAbstraction
						&& !seGraph.anyGraphConstructionStepInQueueMatchesPredicate(isStepForCallAbstraction(nonGeneralizedEntryNode))) {
					if (!settings.onlyUseEntryStateInstanceIfSameNumberOfAllocations
							|| state.getAllocations().size() == callAbstractionState.getAllocations().size()) {
						entryStatesToSearchInstanceIn.add(state);
					}
				}

			}

			LLVMMergeResult mergeRes = getLLVmParameters().SMTsolver.stateFactory
					.searchBestInstance(callAbstractionState, entryStatesToSearchInstanceIn, getAborter());

			if (mergeRes.getGeneralizedState() == null) {
				return null; // no generalization found
			} else {
				return new Pair<>(mergeRes, entryStatesToEntryNodes.get(mergeRes.getOlderState()));
			}

		} else {
			return null; // we are not supposed to look for instances
		}
		

	}

	public Pair<LLVMMergeResult, Node<LLVMAbstractState>> searchGeneralizationOrMergeReturnNode(
			Node<LLVMAbstractState> returnNode,
			LLVMSEGraph seGraph, LLVMFunctionGraph fg) throws MemoryLeakException {
		String function = returnNode.getObject().getCurrentFunction();
		if(recursiveFunctions.contains(function)) {
			return searchGeneralizationOrMergeReturnNode(returnNode, settingsForRecursiveFunctions, seGraph, fg);
		} else {
			return searchGeneralizationOrMergeReturnNode(returnNode, settingsForNonRecursiveFunctions, seGraph, fg);
		}
	}

	// return null if we didn't find an instance and don't have to merge
	// the second component is the node of the merge partner (merge case)/ the
	// generalization (instance case)
	private Pair<LLVMMergeResult, Node<LLVMAbstractState>> searchGeneralizationOrMergeReturnNode(
			Node<LLVMAbstractState> returnNode, IntersectionSettings settings,
			LLVMSEGraph seGraph, LLVMFunctionGraph fg) throws MemoryLeakException {
		LLVMAbstractState returnState = returnNode.getObject();



		Set<Node<LLVMAbstractState>> otherReturnNodesAtSameProgPosSameProgVars = fg.getNonGeneralizedReturnNodes()
				.stream()
				.filter(n -> n != returnNode &&  haveMatchingStacks(n.getObject(),returnState, false))
				//do not consider those return nodes for which we still have a step in the queue:
				///(i.e., it will be treated later by itself)
				.filter(n -> !seGraph.anyGraphConstructionStepInQueueMatchesPredicate(isStepForReturnNode(n)))
				.collect(Collectors.toCollection(LinkedHashSet::new));


		Map<LLVMAbstractState, Node<LLVMAbstractState>> returnStatesToNodes = new  LinkedHashMap<>();
		for(Node<LLVMAbstractState> potentialPartner : otherReturnNodesAtSameProgPosSameProgVars) {
			returnStatesToNodes.put(potentialPartner.getObject(),potentialPartner);
		}

		Set<Node<LLVMAbstractState>> returnNodeToMergeWith = settings.returnStateMergingStrategy.mustMergeWith(fg, returnNode, otherReturnNodesAtSameProgPosSameProgVars);
		
		Set<LLVMAbstractState> returnStatesToMergeWith = returnNodeToMergeWith
				.stream()
				.map(n -> n.getObject())
				.collect(Collectors.toCollection(LinkedHashSet::new));
	
		

		if(!returnNodeToMergeWith.isEmpty()) {
			if(Globals.useAssertions) {
				assert !returnNodeToMergeWith.contains(returnNode) : "Asked to merge with itself";
			}

			//We have found older entry states which we must merge with
			LLVMMergeResult mergeRes = getLLVmParameters().SMTsolver.stateFactory.merge(returnState, returnStatesToMergeWith,
					true, false, getAborter());
			if (mergeRes.getGeneralizedState() == null) {
				throw new IllegalStateException("Was supposed to merge return nodes but failed");
			}

			return new Pair<>(mergeRes, returnStatesToNodes.get(mergeRes.getOlderState()));
		}

		//If we come here, we didn't find a node we had to merge with.
		//If the strategy tells us to, we look if we can still find a generalization (without merging)
		if (settings.searchReturnStateInstanceIfMergingNotEnfored){
			Set<LLVMAbstractState> otherReturnStatesAtSameProgPosSameProgVars = otherReturnNodesAtSameProgPosSameProgVars
					.stream()
					.map(node -> node.getObject())
					.collect(Collectors.toCollection(LinkedHashSet::new));
			
			Set<LLVMAbstractState> returnStatesToSearchInstanceIn = new LinkedHashSet<>();
			for(LLVMAbstractState otherReturnState : otherReturnStatesAtSameProgPosSameProgVars) {
				if (!settings.onlyUseReturnStateInstanceIfSameNumberOfAllocations
						|| otherReturnState.getAllocations().size() == returnState.getAllocations().size()) {
					returnStatesToSearchInstanceIn.add(otherReturnState);
				}
			}

			if(Globals.useAssertions) {
				assert !otherReturnNodesAtSameProgPosSameProgVars.contains(returnNode) : "Asked to merge with itself";
			}

			LLVMMergeResult mergeRes = getLLVmParameters().SMTsolver.stateFactory
					.searchBestInstance(returnState, returnStatesToSearchInstanceIn, getAborter());

			if (mergeRes.getGeneralizedState() == null) {
				return null; //no generalization found
			} else {
				return new Pair<>(mergeRes, returnStatesToNodes.get(mergeRes.getOlderState()));
			}
			
		} else {
			return null; //we are not supposed to look for instances
		}

	}
    
    
    

    public boolean isReturnState(LLVMAbstractState state) {
    	LLVMInstruction currentInstruction = state.getCurrentInstruction();
    	String function = state.getCurrentFunction();
    	return state.getCallStack().isEmpty() //only one stack frame
    			&& (recursiveFunctions.contains(function) || nonRecursiveIntersectableFunctions.contains(function))
    			&& currentInstruction instanceof LLVMRetInstruction;
    }
    

    public  boolean isCallState(LLVMAbstractState state) {
    	if(state.getCallStack().size() > 0) {
    		LLVMProgramPosition pos = state.getProgramPosition();
    		String functionName = state.getCurrentFunction();
    		
    		boolean isCallState = pos.isFunctionStart(module)
    				&& (recursiveFunctions.contains(functionName) || nonRecursiveIntersectableFunctions.contains(functionName));
    		
    		if(Globals.useAssertions) {
    			assert !isCallState || !state.isRefined() : "Graph Consistency Error: Call States should never be refined";
    		}
    		return isCallState;
    	}
    	return false;
    }
    
    public boolean useReturnStateRelationsWhenSummarizing(String function) {
    	return true;//recursiveFunctions.contains(function);
    }
    
    public boolean useReturnStateAllocationsWhenSummarizing(String function) {
    	return true;//recursiveFunctions.contains(function);
    }
    
    public boolean useReturnStateHeapEntriesWhenSummarizing(String function) {
    	return true;//recursiveFunctions.contains(function);
    }
    
	public Triple<LLVMSymbolicVariableRenamingRelationEvaluator, LLVMAllocationDeallocationEvaluator, LLVMUnchangedMemoryRelationEvaluator> createEvaluators(
			Node<LLVMAbstractState> callNode, Node<LLVMAbstractState> returnNode, Set<LLVMSEPath> executionPaths, LLVMImmutableFunctionGraph fg, LLVMModule module, LLVMRelationFactory relationFactory,
			Abortion aborter) {

		LLVMSymbolicVariableRenamingRelationEvaluator renamingEvaluator = null;
		LLVMAllocationDeallocationEvaluator deallocationEvaluator = null;
		LLVMUnchangedMemoryRelationEvaluator unchangedEvaluator = null;

		String function = fg.getFunction();
		if (recursiveFunctions.contains(function)) {
			renamingEvaluator = new LLVMRecursiveSymbolicVariableRenamingRelationEvaluator(fg, executionPaths, module);
			deallocationEvaluator = new LLVMRecursiveAllocationDeallocationEvaluator(fg, executionPaths, module);
			unchangedEvaluator = new LLVMCycleAwareUnchangedMemoryRelationEvaluator(fg, executionPaths, renamingEvaluator, deallocationEvaluator, module, aborter);
			
		} else {
			//Pair<Node<LLVMAbstractState>,Node<LLVMAbstractState>> callReturnNodePair = Helpers.extraCallAndReturnNodeFromExecutionPaths(executionPaths);
			renamingEvaluator = new LLVMStateBasedSymbolicVariableRenamingRelationEvaluator(fg, callNode, returnNode, module);
			/*LLVMSimpleAllocationDeallocationEvaluator simpleAllocationEvaluator = new LLVMSimpleAllocationDeallocationEvaluator(
					callNode,returnNode,executionPaths.iterator().next(), fg, module);
			deallocationEvaluator = simpleAllocationEvaluator;
			unchangedEvaluator = new LLVMSimpleUnchangedMemoryRelationEvaluator(callNode, returnNode, executionPaths.iterator().next(),
					simpleAllocationEvaluator, fg, module, aborter);
					*/
			deallocationEvaluator = new LLVMStateBasedAllocationDeallocationEvaluator(fg, executionPaths, renamingEvaluator, module);
			unchangedEvaluator = new LLVMStateBasedUnchangedMemoryRelationEvaluator(fg, executionPaths, deallocationEvaluator, module, aborter);
		}

		return new Triple<>(renamingEvaluator, deallocationEvaluator, unchangedEvaluator);
	}
	
	public Set<Node<LLVMAbstractState>> nodesNotToFollowWhenSearchingUnneededNodesAfterGeneralization(LLVMFunctionGraphTracker tracker) {
		Set<Node<LLVMAbstractState>> entryNodesOfNonRecFunctions = new LinkedHashSet<>();
		
		for(LLVMFunctionGraph fg : tracker.getAllFunctionGraphs()) {
			if(nonRecursiveIntersectableFunctions.contains(fg.getFunction())) {
				entryNodesOfNonRecFunctions.addAll(fg.getNonGeneralizedEntryNodes());
			}
		}
		
		return entryNodesOfNonRecFunctions;
	}
	
	public boolean isIntersectedState(LLVMAbstractState state) {
		if(state.getCallStack().size() > 0) {
			if(state.getCurrentInstruction() instanceof LLVMRetInstruction) {
				String currentFunction = state.getCurrentFunction();
				return isIntersectableFunction(currentFunction);
			}
		}
		return false;
	}
    
	public boolean canMergeEvaluationOfIntersectedState(LLVMAbstractState intersectedState) {
		String currentFunction = intersectedState.getCurrentFunction(); 
		return nonRecursiveIntersectableFunctions.contains(currentFunction);
	}
	

    public boolean isCallAbstractionOrEntryState(LLVMAbstractState state) {
    	String function = state.getCurrentFunction();
    	
    	return state.getCallStack().isEmpty()
    			&& (recursiveFunctions.contains(function) || nonRecursiveIntersectableFunctions.contains(function)) 
    			&& state.getProgramPosition().isFunctionStart(module) 
    			&& !state.isRefined();
    }
    
    /*public boolean isIntersectedState(LLVMAbstractState state) {
    	String function = state.getCurrentFunction();
    	return !state.getCallStack().isEmpty()
    			&& (recursiveFunctions.contains(function) || nonRecursiveIntersectableFunctions.contains(function)) 
    			&& state.getProgramPosition().isFunctionStart(module) 
    			&& !state.isRefined();
    }*/
    
    public boolean bottomMostFunctionIntersectable(LLVMAbstractState state) {
    	String bottomMostFunction = state.getBottommostFunctionInStack();
    	
    	return (recursiveFunctions.contains(bottomMostFunction)
				|| nonRecursiveIntersectableFunctions.contains(bottomMostFunction));
    }

    public boolean isIntersectableFunction(String functionName) {
    	return (recursiveFunctions.contains(functionName)
				|| nonRecursiveIntersectableFunctions.contains(functionName));
	}

    
    /*public static String functionAfterEvaluationOfState(LLVMAbstractState stateToBeEvaluated) {
    	LLVMInstruction instrToEvaluate = stateToBeEvaluated.getCurrentInstruction();
    	if(instrToEvaluate instanceof LLVMCallInstruction) {
    		LLVMCallInstruction callInstr = (LLVMCallInstruction) instrToEvaluate;
    		return callInstr.getFunctionName().getNameWithoutScope();
    	} else if(instrToEvaluate instanceof LLVMRetInstruction) {
    		return stateToBeEvaluated.getCallStack().getFirst().getProgPos().getFunction();
    	} else {
    		return stateToBeEvaluated.getCurrentFunction();
    	}
    	
    }
    
    public boolean shouldRemoveNonLiveVariablesFromState(LLVMAbstractState state) {
    	if(Globals.useAssertions) {
    		assert recursiveFunctions.contains(function) || nonRecursiveIntersectableFunctions.contains(function);
    	}
    	return nonRecursiveIntersectableFunctions.contains(function);
    }*/
    
    public boolean shouldRemoveNonLiveVariablesFromStatesEvaluationResult(LLVMAbstractState stateToBeEvaluated) {
    	LLVMInstruction instrToEvaluate = stateToBeEvaluated.getCurrentInstruction();
    	if(instrToEvaluate instanceof LLVMCallInstruction) {
    		LLVMCallInstruction callInstr = (LLVMCallInstruction) instrToEvaluate;
    		String calledFunction =  callInstr.getFunctionName().getNameWithoutScope();
    		if(recursiveFunctions.contains(calledFunction) || nonRecursiveIntersectableFunctions.contains(calledFunction)) {
    			//the result will be a call state. we take care of things like live variable analysis once we create its call abstraction
    			return false;
    		}
    		
    	}
    	String bottomMostFunction = stateToBeEvaluated.getBottommostFunctionInStack();
    	
    	return nonRecursiveIntersectableFunctions.contains(bottomMostFunction);
    }
    
    public boolean keepSubGraphsForFunctionWhenRemovingUnneededNodesAferGeneralization(LLVMAbstractState entryState) {
    	//currently disabled, did not seem to help
    	return false;
    }
    
    /*private LLVMFunctionGraph getFunctionGraphForFunction(String functionName) {
		throw new NotImplementedException();
	}*/

	private LLVMParameters getLLVmParameters() {
		return parameters;
	}

	private Abortion getAborter() {
		return aborter;
	}

	/*private LLVMSEGraph getSEGraph() {
		throw new NotImplementedException();
	}*/

	public static boolean  haveMatchingStacks(LLVMAbstractState callState1, LLVMAbstractState callState2, boolean stackFramesMustHaveSameNumberOfAllocations) {
		if(callState1.getCallStack().size() != callState2.getCallStack().size())
			return false;

		//compare topmost frames:
		if(!callState1.getProgramPosition().equals(callState2.getProgramPosition()) ||
				(stackFramesMustHaveSameNumberOfAllocations && callState1.getAllocatedInCurrentFunctionFrame().size() != callState1.getAllocatedInCurrentFunctionFrame().size()) ||
				!callState1.getProgramVariables().keySet().equals(callState2.getProgramVariables().keySet()))
			return false;
		

		Iterator<LLVMReturnInformation> stack1It = callState1.getCallStack().iterator();
		Iterator<LLVMReturnInformation> stack2It = callState2.getCallStack().iterator();

		while(stack1It.hasNext()) {
			LLVMReturnInformation frame1 = stack1It.next();
			LLVMReturnInformation frame2 = stack2It.next();

			if(!frame1.getProgPos().equals(frame2.getProgPos()) ||
					(stackFramesMustHaveSameNumberOfAllocations && frame1.getAllocationsInFunction().size() != frame2.getAllocationsInFunction().size()) ||
					!frame1.getProgramVariables().keySet().equals(frame2.getProgramVariables().keySet()))
				return false;
		}

		return true;
	}
	
	Predicate<LLVMAbstractGraphConstructionStep> isStepForReturnNode(Node<LLVMAbstractState> returnNode) {
		return step -> (step instanceof LLVMHandleReturnStateStep)
				&& (((LLVMHandleReturnStateStep) step).getReturnNode() == returnNode);

	}
	
	Predicate<LLVMAbstractGraphConstructionStep> isStepForCallAbstraction(Node<LLVMAbstractState> callAbstraction) {
		return step -> (step instanceof LLVMHandleCallAbstractionStep)
				&& (((LLVMHandleCallAbstractionStep) step).getCallAbstractionNode() == callAbstraction);

	}
	
	public boolean isFunctionPathAgnostic(String function) {
		return nonRecursiveIntersectableFunctions.contains(function);
	}
	
	//may be called for non-intersectable functions
	public boolean trackVariableRenamingsInStateForFunction(String function) {
		return nonRecursiveIntersectableFunctions.contains(function);
	}
	
	//may be called for non-intersectable functions
	public boolean trackAllocationModificationInStateForFunction(String function) {
		return nonRecursiveIntersectableFunctions.contains(function);
	}

}
