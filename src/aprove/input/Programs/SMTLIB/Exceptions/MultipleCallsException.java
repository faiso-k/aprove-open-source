package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class MultipleCallsException extends RecognitionException {
    private final String s;

    public MultipleCallsException(final String s) {
        this.s = "Command '" + s + "' must not be called multiple times.";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
