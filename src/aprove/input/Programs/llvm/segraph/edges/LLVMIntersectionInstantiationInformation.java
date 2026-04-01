package aprove.input.Programs.llvm.segraph.edges;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.states.*;

public class LLVMIntersectionInstantiationInformation extends LLVMInstantiationInformation {

	public LLVMIntersectionInstantiationInformation(LLVMAbstractState sourceState) {
		super(Collections.emptySet(), createIdentityMap(sourceState));
	}
	
	private static Map<LLVMSimpleTerm, LLVMSimpleTerm> createIdentityMap(LLVMAbstractState state) {
		Map<LLVMSimpleTerm, LLVMSimpleTerm> refMap = new LinkedHashMap<>();
		for(LLVMSymbolicVariable var : state.getSymbolicVariables()) {
			refMap.put(var, var);
		}
		
		return refMap;
	}
	
	@Override
	public String getDotLabel() {
		return "Intersection Instantiation";
	}

}
