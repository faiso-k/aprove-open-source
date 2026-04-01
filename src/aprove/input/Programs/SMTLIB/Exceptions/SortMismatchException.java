package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class SortMismatchException extends RecognitionException {
    private final String s;

    public SortMismatchException(final String s) {
        this.s =
            "Declaration and definition do not fit for identifier '" + s + "'";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
