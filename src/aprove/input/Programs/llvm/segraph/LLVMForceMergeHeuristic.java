package aprove.input.Programs.llvm.segraph;

import java.util.List;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.static_analysis.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Here we collectively decide when we must merge states
 * 
 * @author frankem
 *
 */
public class LLVMForceMergeHeuristic {
	
	private LLVMIntersectionHeuristics intersectionHeuristics;
	
	/**
	 * Number of conditional branching instructions from which on we force merging its states
	 * that are at the same program position
	 */
	private static final int NUMBER_OF_CONDITIONAL_BRANCHES_IN_FUNCTION_FORCING_MERGE = 8;
	
	public LLVMForceMergeHeuristic(LLVMModule module, LLVMIntersectionHeuristics intersectionHeuristics) {
		instructionCounter = new LLVMFunctionInstructionCounter(module);
		this.intersectionHeuristics = intersectionHeuristics;
	}
	
	private final LLVMFunctionInstructionCounter instructionCounter;
	
	private int getUncondBranchCountForFunctionsInStack(LLVMAbstractState state) {
		String function = state.getCurrentFunction();
		
		int condBranchCountOfFunctionsInStack =  
				instructionCounter.getInstructionCountsForFunction(function).getOrDefault(LLVMCondBrInstruction.class,0);

		condBranchCountOfFunctionsInStack += state.getCallStack()
			.stream()
			.mapToInt(frame -> instructionCounter.getInstructionCountsForFunction(frame.getProgPos().getFunction()).getOrDefault(LLVMCondBrInstruction.class,0))
			.sum();
		
		return condBranchCountOfFunctionsInStack;

	}
	
	public boolean needFastConvergenceForState(LLVMAbstractState state) {
		if(intersectionHeuristics.bottomMostFunctionIntersectable(state)) {
			if(getUncondBranchCountForFunctionsInStack(state) >= NUMBER_OF_CONDITIONAL_BRANCHES_IN_FUNCTION_FORCING_MERGE) {
				return true;
			} 
		}
		return false;
	}

	//existingNodesAtSameBlock have same stack size
	//returns pair (x,y) where x indicates that we should generalize and y indicates whether an aggressive merge is necessary 
	public Pair<Boolean,Boolean> haveToGeneralize(
			LLVMSEGraph seGraph,
			Node<LLVMAbstractState> newNode,
			List<Node<LLVMAbstractState>> existingNodesAtSameBlock,
			Abortion aborter) {
		if(existingNodesAtSameBlock.isEmpty()) {
			return new Pair<>(false,false);
		}
		
		
		LLVMAbstractState newState = newNode.getObject();
		String function = newState.getCurrentFunction();
		
		
		
		boolean hasStateWithMatchingStack = existingNodesAtSameBlock
				.stream()
				.anyMatch(n -> LLVMIntersectionHeuristics.haveMatchingStacks(newState,n.getObject(),false));
		
		if(hasStateWithMatchingStack) {
			//If we have too much branching within the function (-> path explosion...) we force merging
			if(needFastConvergenceForState(newState)) {
				if(Globals.DEBUG_FEMRICH) {
					System.err.println("Forcing merge due to " + Integer.toString(getUncondBranchCountForFunctionsInStack(newState)) 
						+ " >= " + NUMBER_OF_CONDITIONAL_BRANCHES_IN_FUNCTION_FORCING_MERGE + " unconditional branches in functions in stack " + 
							newState.getCurrentFunction() +","+ newState.getCallStack().stream().map(frame -> frame.getProgPos().getFunction()).collect(Collectors.joining(",")));
				}
				return new Pair<>(true,true);
			}
		}
		
		
		boolean haveToGeneralize = false;
		for (Node<LLVMAbstractState> node : existingNodesAtSameBlock) {

            // check if this is a repetition, then we have to generalize
			//This is the condition that has always been used
            haveToGeneralize |= seGraph.hasPathNotSteppingOverUnneededNodes(node, newNode);
            if(haveToGeneralize)
            	break;
        }
		
		return new Pair<>(haveToGeneralize,false);
	}
}
