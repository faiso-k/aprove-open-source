package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class TermSortException extends RecognitionException {
    private final String s;

    public TermSortException(final String s) {
        this.s = "Wrapper does not contain '" + s + "'";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
