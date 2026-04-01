package aprove.input.Programs.llvm.utils.static_analysis;

import aprove.input.Programs.llvm.internalStructures.module.*;

public class CommonHelpers {
	
	
	static boolean isExternalFunction(String function, LLVMModule module) {
		LLVMFnDeclaration decl = module.getFunctions().get(function);
		
		return !(decl instanceof LLVMFnDefinition);
	}
}
