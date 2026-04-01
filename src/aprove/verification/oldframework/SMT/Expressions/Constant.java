package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public abstract class Constant<V extends Sort> extends SMTExpression<V> {
    private final Object constant;

    public Constant(V t, Object constant) {
        super(t);
        assert constant != null;
        assert constant.getClass() == t.getRepresentingClass();
        this.constant = constant;
    }

    public Object getConstant() {
        return this.constant;
    }
}
