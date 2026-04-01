package aprove.input.Programs.llvm.exceptions;

/**
 * @author Jera Hensel
 * Thrown if during the construction of an LLVMSEGraph an ERROR state is reached.
 */
public class ErrorStateException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 5932986281408896424L;

    /**
     * Creates an assertion exception with a default message.
     * @param nodeNumber The number of the node where the violation happened.
     */
    public ErrorStateException(final int nodeNumber) {
        super("ERROR state may be reached (node " + nodeNumber + ")!");
    }

}
