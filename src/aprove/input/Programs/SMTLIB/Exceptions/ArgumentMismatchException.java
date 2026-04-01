package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class ArgumentMismatchException extends RecognitionException {
    private final String s =
        "Can't apply the function to the arguments. Sorts of the arguments mismatch.";

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
