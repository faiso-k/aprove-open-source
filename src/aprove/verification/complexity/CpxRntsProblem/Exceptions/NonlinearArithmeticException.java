package aprove.verification.complexity.CpxRntsProblem.Exceptions;

import aprove.verification.dpframework.BasicStructures.*;

@SuppressWarnings("serial")
public class NonlinearArithmeticException extends Exception {

    private final TRSTerm term;

    public NonlinearArithmeticException(TRSTerm term) {
        this.term = term;
    }

    @Override
    public String getMessage() {
        return "TRSTerm contains nonlinear arithmetic: " + this.term.toString();
    }
}
