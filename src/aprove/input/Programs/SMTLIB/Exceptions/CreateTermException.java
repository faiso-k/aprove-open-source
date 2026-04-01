package aprove.input.Programs.SMTLIB.Exceptions;

import org.antlr.runtime.*;

public class CreateTermException extends RecognitionException {
    private final String s;

    public CreateTermException(final String s) {
        this.s = "Can't create term out of '" + s + "'";
    }

    @Override
    public String getMessage() {
        return super.getMessage() + "\n" + this.s;
    }
}
