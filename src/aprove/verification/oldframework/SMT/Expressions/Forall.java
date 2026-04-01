package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class Forall<S extends Sort> extends SMTExpression<S> {
    private final SMTExpression<? extends S> body;
    private final ImmutableList<? extends Symbol0<?>> vars;

    public Forall(S t, ImmutableList<? extends Symbol0<?>> vars, SMTExpression<? extends S> body) {
        super(t);
        this.vars = vars;
        this.body = body;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public SMTExpression<? extends S> getBody() {
        return this.body;
    }

    public ImmutableList<? extends Symbol0<?>> getVars() {
        return this.vars;
    }

}
