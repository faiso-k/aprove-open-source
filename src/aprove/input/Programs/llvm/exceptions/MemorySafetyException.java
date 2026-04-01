package aprove.input.Programs.llvm.exceptions;

/**
 * Thrown if the construction of an LLVMSEGraph does not prove memory safety.
 * @author unknown, CryingShadow
 */
public class MemorySafetyException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -7223020223890991393L;

    /**
     * Creates a memory safety exception with a default message.
     * @param nodeNumber The number of the node where the violation happened.
     */
    public MemorySafetyException(int nodeNumber) {
        super("Program cannot be proven to be memory safe (node " + nodeNumber + ")!");
    }

    /**
     * Passthrough.
     * @param string The error message.
     */
    public MemorySafetyException(String string) {
        super(string);
    }

}
