package aprove.input.Programs.llvm.internalStructures.instructions;

/**
 * Super class for terminator instructions.
 * @author CryingShadow
 */
public abstract class LLVMTerminatorInstruction extends LLVMInstruction {

    /**
     * @param debugLine The index of the line with debug information.
     * Default constructor.
     */
    public LLVMTerminatorInstruction(int debugLine) {
        super(debugLine);
    }

}
