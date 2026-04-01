package aprove.input.Programs.llvm.exceptions;

/**
 * @author CryingShadow
 * Thrown if the construction of an LLVMSEGraph does not prove satisfaction of all assertions.
 */
public class AssertionException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -2327739597423009985L;

    /**
     * Creates an assertion exception with a default message.
     * @param nodeNumber The number of the node where the violation happened.
     */
    public AssertionException(final int nodeNumber) {
        super("Program cannot be proven to satisfy its assertions (node " + nodeNumber + ")!");
    }

}
