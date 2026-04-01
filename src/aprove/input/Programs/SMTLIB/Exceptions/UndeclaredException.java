package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class UndeclaredException extends RecognitionException {
    private final String s;

    public UndeclaredException(final String s) {
        this.s = "Identifier '" + s + "' is not declared.";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
