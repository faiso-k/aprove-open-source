package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class Call3<RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> extends Call<RV> {
    private final SMTExpression<A0> a0;
    private final SMTExpression<A1> a1;
    private final SMTExpression<A2> a2;
    private final Symbol3<? extends Sort, A0, A1, A2> sym;

    /**
     * Special constructor that allows to overwrite the return type of the Call3
     * for polymorphic symbols. Only used for if-then-else.
     * @param sym
     * @param r
     * @param a0
     * @param a1
     * @param a2
     */
    public Call3(Symbol3<? extends Sort, A0, A1, A2> sym, RV r, SMTExpression<A0> a0, SMTExpression<A1> a1, SMTExpression<A2> a2)
    {
        super(r);
        assert sym.getReturnSort().getClass().isAssignableFrom(r.getClass());
        this.sym = sym;
        this.a0 = a0;
        this.a1 = a1;
        this.a2 = a2;
    }

    public Call3(Symbol3<RV, A0, A1, A2> sym, SMTExpression<A0> a0, SMTExpression<A1> a1, SMTExpression<A2> a2) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.a0 = a0;
        this.a1 = a1;
        this.a2 = a2;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public SMTExpression<A0> getA0() {
        return this.a0;
    }

    public SMTExpression<A1> getA1() {
        return this.a1;
    }

    public SMTExpression<A2> getA2() {
        return this.a2;
    }

    @Override
    public Symbol3<? extends Sort, A0, A1, A2> getSym() {
        return this.sym;
    }
}
