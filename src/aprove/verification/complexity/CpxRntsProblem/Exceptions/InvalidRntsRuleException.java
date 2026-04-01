package aprove.verification.complexity.CpxRntsProblem.Exceptions;

import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

@SuppressWarnings("serial")
public class InvalidRntsRuleException extends Exception {

    private final TRSFunctionApplication lhs;
    private final TRSTerm rhs;
    private final ImmutableSet<Constraint> constraints;
    private final String msg;

    public InvalidRntsRuleException(
            final TRSFunctionApplication l,
            final TRSTerm r,
            final ImmutableSet<Constraint> c,
            final String msg) {
        this.lhs = l;
        this.rhs = r;
        this.constraints = c;
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return this.lhs.toString() + " -> " + this.rhs.toString() + " " + this.constraints.toString() + ": " + this.msg;
    }
}
