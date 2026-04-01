package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import immutables.*;

public class Let<S extends Sort> extends SMTExpression<S> {
    private final ImmutableList<VarBinding<?>> bindings;
    private final SMTExpression<S> body;

    Let(S t, ImmutableList<VarBinding<?>> bindings, SMTExpression<S> body) {
        super(t);
        this.bindings = bindings;
        this.body = body;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public ImmutableList<VarBinding<?>> getBindings() {
        return this.bindings;
    }

    public SMTExpression<S> getBody() {
        return this.body;
    }
}
