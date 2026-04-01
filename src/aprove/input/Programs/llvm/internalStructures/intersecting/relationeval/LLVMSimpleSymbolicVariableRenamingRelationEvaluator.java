package aprove.input.Programs.llvm.internalStructures.intersecting.relationeval;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

//just uses program variables
public class LLVMSimpleSymbolicVariableRenamingRelationEvaluator extends LLVMSymbolicVariableRenamingRelationEvaluator{

    //private Set<LLVMSEPath> executionPaths;
    private final LLVMAbstractState callState;
    private final LLVMAbstractState returnState;



    private Map<LLVMSymbolicVariable,Set<LLVMSymbolicVariable>> cache;



    //execution paths from same call to same return state
    public LLVMSimpleSymbolicVariableRenamingRelationEvaluator(
    		LLVMImmutableFunctionGraph fg,
    		Node<LLVMAbstractState> callNode,
    		Node<LLVMAbstractState> returnNode,
    		LLVMModule module) {
        super(fg,callNode,returnNode,module);
        callState = callNode.getObject();
        returnState = returnNode.getObject();

        cache = new LinkedHashMap<>();
        for(Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> ce : callState.getProgramVariables().entrySet() ) {
            for(Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> re : returnState.getProgramVariables().entrySet() ) {
                if(ce.getKey().equals(re.getKey())) {
                    //Same variable

                    //get set for call state variable
                    Set<LLVMSymbolicVariable> cacheEntry = cache.computeIfAbsent(ce.getValue().x, c -> new LinkedHashSet<>());
                    
                    
                    cacheEntry.add(re.getValue().x);
                }
            }
        }


    }


    @Override
    public Set<LLVMSymbolicVariable> getReturnStateVariablesForCallStateVariable(LLVMSymbolicVariable callStateVar) {
        return cache.computeIfAbsent(callStateVar, v -> Collections.emptySet());

    }


	@Override
	protected SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> getGraph() {
		return fg.getGraph();
	}
	
	@Override
	public boolean isVariableConsistetOnCycles(Node<LLVMAbstractState> node, LLVMSymbolicVariable var) {
		throw new UnsupportedOperationException();
	}
}
