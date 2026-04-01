package aprove.verification.complexity.CpxRntsProblem.Exceptions;

import aprove.verification.dpframework.BasicStructures.*;

@SuppressWarnings("serial")
public class InvalidRntsRuleConstraintException extends Exception {

    private final TRSTerm constraintTerm;
    private final String msg;

    public InvalidRntsRuleConstraintException(final TRSTerm constraintTerm, final String msg) {
        this.constraintTerm = constraintTerm;
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return "Invalid constraint term: " + this.constraintTerm + ": " + this.msg;
    }
}
