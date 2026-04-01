package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class MultipleOccurenceException extends RecognitionException {
    private final String s;

    public MultipleOccurenceException(final String s) {
        this.s = "Identifier '" + s + "' already declared.";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
