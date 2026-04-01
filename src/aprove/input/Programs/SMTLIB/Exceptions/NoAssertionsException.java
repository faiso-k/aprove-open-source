package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class NoAssertionsException extends RecognitionException {
    private final String s = "There is nothing on the assertion-stack";

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
