package aprove.input.Programs.llvm.utils.static_analysis;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.edges.*;

public class LLVMFunctionInstructionCounter {
	
	public LLVMFunctionInstructionCounter(LLVMModule module) {
		this.module = module;
	}
	
	private final LLVMModule module;
	
	private Map<String,Map<Class<? extends LLVMInstruction>, Integer>> cache;
	
	private Map<String,Integer> callsOfFunctionCache;
	
	
	public Map<Class<? extends LLVMInstruction>, Integer> getInstructionCountsForFunction(String function) {
		if(cache == null) {
			computeCounts();
		}
		return cache.get(function);
	}
	
	public int getNumberOfInstructionsOfFunctionAndType(String function, Class<? extends LLVMInstruction> instrClass) {
		if(CommonHelpers.isExternalFunction(function, module)) {
			return 0;
		}
		return getInstructionCountsForFunction(function).getOrDefault(instrClass, 0);
	}
	
	/**
	 * How often is the given function called (externally or by itself)
	 * Function name without leading @
	 */
	public int getNumberOfCallsOfFunction(String function) {
		if(callsOfFunctionCache == null) {
			computeCounts();
		}
		return callsOfFunctionCache.getOrDefault(function,0);
	}
	
	
	private void computeCounts() {
		Map<String, LLVMFnDeclaration> functionMap = module.getFunctions();

		Set<LLVMProgramPosition> allProgramPositions = LLVMModule.getAllPositions(functionMap.values());
		
		Map<String,Map<Class<? extends LLVMInstruction>, Integer>> functionsToInstrToCount = new LinkedHashMap<>(); 
		callsOfFunctionCache = new LinkedHashMap<>();
		
		for(LLVMProgramPosition progPos : allProgramPositions) {
			String curFunc = progPos.getFunction();
			LLVMInstruction instr = module.getInstruction(progPos);
			Class<? extends LLVMInstruction> clazz = instr.getClass();
			
			Map<Class<? extends LLVMInstruction>, Integer> instrMapForFunction = 
					functionsToInstrToCount.computeIfAbsent(curFunc, func -> new LinkedHashMap<>());
			
			if(instr instanceof LLVMCallInstruction) {
				LLVMCallInstruction callInstr = (LLVMCallInstruction) instr;
				String calledFunction = callInstr.getFunctionName().getName().substring(1);
				
				int currentCount = callsOfFunctionCache.getOrDefault(calledFunction, 0);
				callsOfFunctionCache.put(calledFunction, currentCount+1);
			}
			
			
			Integer existingInstrCount = instrMapForFunction.computeIfAbsent(clazz, c -> 0);
			
			instrMapForFunction.put(clazz,existingInstrCount+1);
			
			cache = functionsToInstrToCount;
			
		}

		return;

	}
}
