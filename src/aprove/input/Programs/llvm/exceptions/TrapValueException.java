package aprove.input.Programs.llvm.exceptions;

/**
 * Accessing a possible trap value causes undefined behavior.
 * @author cryingshadow
 * @version $Id$
 */
public class TrapValueException extends UndefinedBehaviorException {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -439999929925634134L;

    /**
     * @param nodeNumber The node number where the exception occurred.
     */
    public TrapValueException(int nodeNumber) {
        super("Accessing possible trap value at node " + nodeNumber + ".");
    }

    /**
     * @param message The message of this exception.
     */
    public TrapValueException(String message) {
        super(message);
    }

}
