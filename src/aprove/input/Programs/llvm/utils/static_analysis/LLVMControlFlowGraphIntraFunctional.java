package aprove.input.Programs.llvm.utils.static_analysis;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMControlFlowGraphIntraFunctional {

	
	
	SimpleGraph<LLVMCFGInstructionNode,String> cfg;
	LinkedHashSet<Cycle<LLVMCFGInstructionNode>> sccs;
	
	Map<LLVMProgramPosition,Node<LLVMCFGInstructionNode>> pposToNode;
	LLVMModule module;
	Set<String> functionsContainingLoop;
	Set<String> functionsCalledFromLoop;
	
	Map<String,Set<String>> calledFunctions;
	
	
	public LLVMControlFlowGraphIntraFunctional(LLVMModule module) {
		this.module = module;
	}
	
	static class LLVMCFGInstructionNode extends Pair<LLVMProgramPosition, LLVMInstruction> {
		public LLVMCFGInstructionNode(LLVMProgramPosition x, LLVMInstruction y) {
			super(x, y);
		}

		LLVMProgramPosition getProgramPosition() {
			return x;
		}
		
		LLVMInstruction getInstruction() {
			return y;
		}
		

	}
	
	
	private final static LLVMInstructionGraphNodeObjectCreator<LLVMCFGInstructionNode> creator = 
			new LLVMInstructionGraphNodeObjectCreator<LLVMCFGInstructionNode>() {

        @Override
        public LLVMCFGInstructionNode create(LLVMModule prog, LLVMProgramPosition pos) {
            return new LLVMCFGInstructionNode(pos, prog.getInstruction(pos));
        }

    };
    
    private void createCFG() {
    	cfg = module.computeInstructionGraph(creator);
    	pposToNode = new LinkedHashMap<>();
    	
    	for(Node<LLVMCFGInstructionNode> node : cfg.getNodes()) {
    		pposToNode.put(node.getObject().x, node);
    	}
    	
    	sccs = cfg.getSCCs();
    	
    }
    
    private void determineLoopingBehavior() {
    	if(cfg == null) {
    		createCFG();
    	}
    	
    	functionsContainingLoop = new LinkedHashSet<>();
    	functionsCalledFromLoop = new LinkedHashSet<>();
    	calledFunctions = new LinkedHashMap<>();
    	
    	for(Cycle<LLVMCFGInstructionNode> scc : sccs) {
			for(Node<LLVMCFGInstructionNode> node : scc) {
				String activeFunction = node.getObject().getProgramPosition().getFunction();
				
				functionsContainingLoop.add(activeFunction);
				
				LLVMInstruction curInstr = node.getObject().y;
				if(curInstr instanceof LLVMCallInstruction) {
					LLVMCallInstruction callInstr = (LLVMCallInstruction) curInstr;
					
					String calledFunction = callInstr.getFunctionName().getNameWithoutScope();
					functionsCalledFromLoop.add(calledFunction);
					
					Set<String> functionsCalledByCurFunction = calledFunctions.computeIfAbsent(activeFunction, x -> new LinkedHashSet<>());
					functionsCalledByCurFunction.add(calledFunction);
				}

			}
		}
    }
    
    /**
     * This does not respect called functions, i.e,
     * will return false if the given function calls a function with a loop,
     * but does not have a loop by itself
     */
    public boolean functionContainsLoop(String functionName) {
    	
    	
    	if(functionsContainingLoop == null) {
    		
    		determineLoopingBehavior();
    	}
    	
    	return functionsContainingLoop.contains(functionName);
    	
    }
    
    
    /**
     * Is there a function call to the given function, where the call instr is in a loop?
     */
    public boolean functionIsCalledFromLoop(String functionName) {
    	if(functionsCalledFromLoop == null) {
    		
    		determineLoopingBehavior();
    	}
    	
    	return functionsCalledFromLoop.contains(functionName);
    	
    }
    
    /**
     * Which functions are called by the given function?
     */
    public Set<String> functionsCalledByFunction(String functionName) {
    	if(calledFunctions == null) {
    		
    		determineLoopingBehavior();
    	}
    	
    	return calledFunctions.getOrDefault(functionName, Collections.emptySet());
    	
    }
    
    public Set<String> getLoopingFunctions() {
    	if(functionsCalledFromLoop == null) {
    		
    		determineLoopingBehavior();
    	}
    	
    	return functionsContainingLoop;
    }
	
}
