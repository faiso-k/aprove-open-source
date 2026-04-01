package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class UnsupportedSortException extends RecognitionException {
    private final String s;

    public UnsupportedSortException(final String s) {
        this.s = s + " is not implemented for this sort.";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
