package aprove.verification.complexity.CpxIntTrsProblem.Exceptions;

import aprove.verification.dpframework.BasicStructures.*;

@SuppressWarnings("serial")
public class NoConstraintTermException extends Exception {
    private final TRSTerm t;

    public NoConstraintTermException(final TRSTerm t) {
        this.t = t;
    }

    @Override
    public String getMessage() {
        return "No condition term: " + this.t.toString();
    }
}
