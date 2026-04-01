package aprove.verification.complexity.CpxIntTrsProblem.Exceptions;

import aprove.verification.dpframework.IDPProblem.*;

@SuppressWarnings("serial")
public class NoValidCpxIntTupleRuleException extends Exception {

    private final IGeneralizedRule rule;
    private final String msg;

    public NoValidCpxIntTupleRuleException(final IGeneralizedRule rule, final String msg) {
        this.rule = rule;
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return this.rule.toString() + ": " + this.msg;
    }
}
