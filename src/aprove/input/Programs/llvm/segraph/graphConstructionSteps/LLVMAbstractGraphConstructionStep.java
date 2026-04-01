package aprove.input.Programs.llvm.segraph.graphConstructionSteps;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Superclass to all graph construction steps.
 * Make sure that they have proper hashCode and equals methods,
 * because they will be stored in a LinkedHashMap were we want to eliminate duplicates there
 * @author Frank Emrich
 *
 */
public abstract class LLVMAbstractGraphConstructionStep {
	
	protected final LLVMSEGraph graph;
	
	private final List<LLVMAbstractGraphConstructionStep> stepsEvokedByGrahpListenersWhilePerformingStep;
	
	LLVMAbstractGraphConstructionStep(LLVMSEGraph graph) {
		this.graph = graph;
		this.stepsEvokedByGrahpListenersWhilePerformingStep = new ArrayList<>(0);
	}

	/**
	 * The hook for actually performing graph construction work
	 */
	abstract public List<LLVMAbstractGraphConstructionStep> perform(Abortion aborter, boolean debug)
			throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException,
			MemoryLeakException;
	
	LLVMParameters getStrategyParameters() {
		return graph.getStrategyParameters();
	}
	
	LLVMModule getModule() {
		return graph.getModule();
	}
	
	/**
	 * 
	 * @return true iff the step should not be executed
	 */
	public abstract boolean isObsolete();
	
	
	/**
	 * 
	 * @param steps A list of <code>LLVMAbstractGraphConstructionStep</code>s that were created 
	 * by a <code>LLVMSEGraphEventListener</code> while performing this step.
	 * They will be enqueued for performing later
	 */
	public void addStepsCreatedByGraphListenersWhilePerforming(List<LLVMAbstractGraphConstructionStep> steps) {		
		stepsEvokedByGrahpListenersWhilePerformingStep.addAll(steps);
		
	}
	
	protected LLVMIntersectionHeuristics getIntersectionHeuristics() {
		return graph.getIntersectionHeuristics();
	}
	

    
    public ImmutableList<LLVMAbstractGraphConstructionStep> getStepsEvokedByGrahpListenersWhilePerformingStep() {
		return ImmutableCreator.create(stepsEvokedByGrahpListenersWhilePerformingStep);
	}

    /*
     * Using this looks like a bad idea, because it does not really support call abstractions.
     * For those, the step is created in the call state step directly
     */
    @Deprecated
	List<LLVMAbstractGraphConstructionStep> createConstructionStepForUnevaluatedNode(Node<LLVMAbstractState> node) {
    	if(node == null)
    		return  Collections.emptyList();
    	
    	LLVMAbstractState state = node.getObject();
    	if(getIntersectionHeuristics().isCallState(state)) {
    		return Collections.singletonList(new LLVMHandleCallStateStep(graph, node));
    	} else if(getIntersectionHeuristics().isReturnState(state)) {
    		return Collections.singletonList(new LLVMHandleReturnStateStep(graph, node)); 
    	}  else if(state.isEnd()) {
    		return Collections.emptyList();
    	}  else {
    		return  Collections.singletonList(new LLVMStandardStep(graph,node));
    	}
    }
    
    

    @Deprecated /* moved to LLVMIntersectionHeuristics, remove here */
    public static String getBottommostFunctionInStack(LLVMAbstractState state) {
    	String result;
		if(state.getCallStack().isEmpty()) {
			result = state.getCurrentFunction();
		} else {
			result = state.getCallStack().getLast().getProgPos().x;
		}
		
		if(Globals.useAssertions) {
			assert !result.startsWith("@");
		}
		return result;
    }
    
    @Deprecated /* moved to LLVMIntersectionHeuristics, remove here */
    public static boolean isReturnState(LLVMSEGraph graph, LLVMAbstractState state) {
    	LLVMInstruction currentInstruction = state.getCurrentInstruction();
    	return state.getCallStack().isEmpty() && graph.isRecursiveFunction(getBottommostFunctionInStack(state)) && currentInstruction instanceof LLVMRetInstruction;
    }
    
    @Deprecated /* moved to LLVMIntersectionHeuristics, remove here */
    public static boolean isCallState(LLVMSEGraph graph, LLVMAbstractState state) {
    	if(state.getCallStack().size() > 0) {
    		LLVMProgramPosition pos = state.getProgramPosition();
    		String functionName = state.getCurrentFunction();
    		
    		return graph.isRecursiveFunction(functionName) && pos.isFunctionStart(graph.getModule()) && !state.isRefined();
    	}
    	return false;
    }
    
    @Deprecated /* moved to LLVMIntersectionHeuristics, remove here */
    public static boolean isCallAbstractionOrEntryState(LLVMSEGraph graph, LLVMAbstractState state) {
    	return state.getCallStack().isEmpty() && 
    			graph.isRecursiveFunction(state.getCurrentFunction()) && 
    			state.getProgramPosition().isFunctionStart(graph.getModule()) && !state.isRefined();
    }
    
    
    

}
