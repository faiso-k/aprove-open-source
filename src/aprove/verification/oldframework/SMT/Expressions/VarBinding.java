package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class VarBinding<V extends Sort> {
    private final SMTExpression<V> expr;
    private final Symbol0<V> var;

    public VarBinding(Symbol0<V> v, SMTExpression<V> e) {
        this.var = v;
        this.expr = e;
    }

    public SMTExpression<V> getExpr() {
        return this.expr;
    }

    public V getType() {
        return this.expr.getType();
    }

    public Symbol0<V> getVar() {
        return this.var;
    }
}
