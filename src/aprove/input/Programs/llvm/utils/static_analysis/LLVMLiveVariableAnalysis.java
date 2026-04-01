package aprove.input.Programs.llvm.utils.static_analysis;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class LLVMLiveVariableAnalysis {
	
	ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> liveVariables;
	
	static class LLVMFunctionLocalLiveness extends Quadruple<LLVMProgramPosition, LLVMInstruction, Set<String>, Set<String>> {
		public LLVMFunctionLocalLiveness(LLVMProgramPosition w, LLVMInstruction x, Set<String> y, Set<String> z) {
			super(w, x, y, z);
		}

		LLVMProgramPosition getProgramPosition() {
			return w;
		}
		
		LLVMInstruction getInstruction() {
			return x;
		}
		
		Set<String> getLiveInVariables() {
			return y;
		}
		
		Set<String> getLiveOutVariables() {
			return z;
		}
	}

	private final static LLVMInstructionGraphNodeObjectCreator<LLVMFunctionLocalLiveness> creator = 
			new LLVMInstructionGraphNodeObjectCreator<LLVMFunctionLocalLiveness>() {

        @Override
        public LLVMFunctionLocalLiveness create(LLVMModule prog, LLVMProgramPosition pos) {
            return new LLVMFunctionLocalLiveness(pos, prog.getInstruction(pos), new LinkedHashSet<String>(), new LinkedHashSet<String>());
        }

    };
	
	
	
    
    public ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> getLiveVariables(LLVMModule module) {
    	if(liveVariables == null) {
	    	Graph<LLVMFunctionLocalLiveness, String> instructionGraph;
	    	
	    	
	    	
	        instructionGraph = module.computeInstructionGraph(creator);
	    	Map<LLVMProgramPosition,Node<LLVMFunctionLocalLiveness>> posToNode = new LinkedHashMap<>();
	        
	        
	    	//initialize pos to node map
	    	//initialze live in sets of each instruction by the operands it uses 
	    	for(Node<LLVMFunctionLocalLiveness> node : instructionGraph.getNodes()) {
	    		LLVMFunctionLocalLiveness livenessObject = node.getObject();
	    		
	    		posToNode.put(livenessObject.getProgramPosition(), node);
	    		
	    		LLVMInstruction instr = livenessObject.getInstruction();
	    		instr.collectUsedVariables(livenessObject.getLiveInVariables());
	    		
	    	}
	    	
	    	boolean changed = false;
	    	do {
	    		changed = false;
	    		
	    		//
	    		for(Node<LLVMFunctionLocalLiveness> liveNode : instructionGraph.getNodes()) {
	    			LLVMFunctionLocalLiveness livenessObject = liveNode.getObject();
	    			LLVMInstruction instr = livenessObject.getInstruction();
	    			
	    			
	    			//if we call a function, the global variables live in at the start are live in here, too
	    			if(instr instanceof LLVMCallInstruction) {
	    				LLVMCallInstruction callInstr = (LLVMCallInstruction) instr;
	    				String calledFunction = callInstr.getFunctionName().getNameWithoutScope();
	    				
	    				LLVMFnDeclaration fnDecl = module.getFunctions().get(calledFunction);
	    				
	    				if(fnDecl instanceof LLVMFnDefinition) {
	    					LLVMFnDefinition actFunction = (LLVMFnDefinition)fnDecl;
	    					LLVMProgramPosition startOfCalledFunction = new LLVMProgramPosition(
	    							calledFunction,
	        						actFunction.getNameOfFirstBlock(), 0);
	    					
	    					Node<LLVMFunctionLocalLiveness> calledFunctionStartNode = posToNode.get(startOfCalledFunction);
	    					
	    					LLVMFunctionLocalLiveness calledFunctionLiveness = calledFunctionStartNode.getObject();
	    					
	    					for(String calledLiveInVar : calledFunctionLiveness.getLiveInVariables()) {
	    						if(calledLiveInVar.startsWith("@")) {
	    							changed |= livenessObject.getLiveInVariables().add(calledLiveInVar);
	    						}
	    					}
	    					
	    				}
	    			}
	    			
	    			
	    			//propagate live in to live out of predecessors
	    			for(Node<LLVMFunctionLocalLiveness> liveNodePred : instructionGraph.getIn(liveNode)) {
	    				LLVMFunctionLocalLiveness predLivenessObject = liveNodePred.getObject();
	    				
	    				changed |= predLivenessObject.getLiveOutVariables().addAll(livenessObject.getLiveInVariables());
	    			}
	    			
	    			
	    			//propagate live out to live in of same node unless assigned:
	    			for(String liveOutVar : livenessObject.getLiveOutVariables()) {
	    				
	    				String producedVariable = instr.getProducedVariable();
	    				
	    				if(!liveOutVar.equals(producedVariable)) {
	    					changed |= livenessObject.getLiveInVariables().add(liveOutVar);
	    				}
	    				
	    				
	    				
	    			}
	    			
	        		
	        	}
	    		
	    		
	    	} while(changed);
	    	
	    	
	    	Map<LLVMProgramPosition, ImmutableSet<String>> result = new LinkedHashMap<>();
	    	for(Node<LLVMFunctionLocalLiveness> node : instructionGraph.getNodes()) {
	    		LLVMFunctionLocalLiveness livenessObject = node.getObject();
	    		
	    		result.put(livenessObject.getProgramPosition(), ImmutableCreator.create(livenessObject.getLiveInVariables()));
	    	}
	    	
	    	
	    	
	    	liveVariables = ImmutableCreator.create(result);
	    }
    	return liveVariables;
    }
    
	
}
