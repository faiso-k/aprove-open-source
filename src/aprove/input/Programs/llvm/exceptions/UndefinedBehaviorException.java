package aprove.input.Programs.llvm.exceptions;

/**
 * @author CryingShadow
 * Thrown if the construction of an LLVMSEGraph does not prove absence of undefined behavior.
 */
public class UndefinedBehaviorException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -7465131197488836837L;

    /**
     * Creates an undefined behavior exception with a default message.
     * @param nodeNumber The number of the node where the violation happened.
     */
    public UndefinedBehaviorException(final int nodeNumber) {
        super("Program cannot be proven to behave in a sufficiently defined way (node " + nodeNumber + ")!");
    }

    /**
     * Creates an undefined behavior exception with the specified message.
     * @param message The error message.
     */
    public UndefinedBehaviorException(final String message) {
        super(message);
    }

    /**
     * Creates an undefined behavior exception with the specified message and appends " (node <nodeNumber>)" to it
     * @param message The error message.
     * @param nodeNumber The number of the node where the violation happened
     */
    public UndefinedBehaviorException(final String message, final int nodeNumber) {
        super(message + " (node " + nodeNumber + ")");
    }
}
