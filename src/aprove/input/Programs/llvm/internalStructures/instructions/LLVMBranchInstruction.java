package aprove.input.Programs.llvm.internalStructures.instructions;

/**
 * Super class for branching instructions.
 * @author CryingShadow
 */
public abstract class LLVMBranchInstruction extends LLVMTerminatorInstruction {

    /**
     * Default constructor.
     */
    public LLVMBranchInstruction(int debugLine) {
        super(debugLine);
    }

}
