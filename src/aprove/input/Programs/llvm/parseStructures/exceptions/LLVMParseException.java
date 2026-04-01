package aprove.input.Programs.llvm.parseStructures.exceptions;

/**
 * Exception to classify all exception thrown in the parser and while building
 * the basic structure.
 *
 * @author Janine Repke
 */
public class LLVMParseException extends Exception {

    private static final long serialVersionUID = -3327387685654008271L;

    public LLVMParseException(String errorMessage) {
        super(errorMessage);
    }

}
