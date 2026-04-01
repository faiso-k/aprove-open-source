package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class UnsupportedException extends RecognitionException {
    private final String s;

    public UnsupportedException(final String s) {
        this.s = s;
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
