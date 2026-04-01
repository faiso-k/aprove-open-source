package aprove.input.Programs.llvm.internalStructures.instructions;

import aprove.input.Programs.llvm.internalStructures.literals.*;

public class LLVMInputArgAwareStoreInstruction extends LLVMStoreInstruction {

    public LLVMInputArgAwareStoreInstruction(LLVMLiteral val, LLVMLiteral addr, LLVMLiteral align, int debugLine) {
        super(val, addr, align, debugLine);
    }
}
