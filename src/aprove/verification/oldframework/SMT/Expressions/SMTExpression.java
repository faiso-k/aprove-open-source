package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;

public abstract class SMTExpression<R extends Sort> {

    private final R t;

    protected SMTExpression(R t) {
        this.t = t;
    }

    public abstract <T> T accept(ExpressionVisitor<T> visitor);

    public R getType() {
        return this.t;
    }

    @Override
    public String toString() {
        return ToStringVisitor.convertExpressionToString(this);
    }
}
