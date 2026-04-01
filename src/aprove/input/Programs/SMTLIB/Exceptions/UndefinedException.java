package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class UndefinedException extends RecognitionException {
    private final String s;

    public UndefinedException(final String s) {
        this.s = "Identifier '" + s + "' is not defined.";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
