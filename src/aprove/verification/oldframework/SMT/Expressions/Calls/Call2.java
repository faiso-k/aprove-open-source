package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class Call2<RV extends Sort, A0 extends Sort, A1 extends Sort> extends Call<RV> {
    private final SMTExpression<A0> a0;
    private final SMTExpression<A1> a1;
    private final Symbol2<RV, A0, A1> sym;

    public Call2(Symbol2<RV, A0, A1> sym, SMTExpression<A0> a0, SMTExpression<A1> a1) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.a0 = a0;
        this.a1 = a1;
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

    @Override
    public Symbol2<RV, A0, A1> getSym() {
        return this.sym;
    }
}
