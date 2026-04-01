package aprove.input.Programs.llvm.exceptions;

/**
 * @author Max Berrendorf
 * Thrown if an invalid use of the method "free" is encountered
 * (either the argument of free is not a pointer returned by a former call of malloc
 *  or a pointer is freed multiple times).
 */
public class InvalidFreeException extends MemorySafetyException {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -3081232189352102708L;

    public InvalidFreeException(int nodeNumber) {
        super("Invalid call of free (node " + nodeNumber + ")!");
    }

}
