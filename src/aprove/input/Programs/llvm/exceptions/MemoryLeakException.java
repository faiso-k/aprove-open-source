package aprove.input.Programs.llvm.exceptions;

/**
 * Thrown if a memory leak is detected.
 * @author unknown, CryingShadow
 */
public class MemoryLeakException extends Exception {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 7762282398899041765L;

    /**
     * @param string The exception message.
     */
    public MemoryLeakException(String string) {
        super(string);
    }

}
