package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class Call1<RV extends Sort, A0 extends Sort> extends Call<RV> {
    private final SMTExpression<A0> a0;
    private final Symbol1<RV, A0> sym;

    public Call1(Symbol1<RV, A0> sym, SMTExpression<A0> a0) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.a0 = a0;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public SMTExpression<A0> getA0() {
        return this.a0;
    }

    @Override
    public Symbol1<RV, A0> getSym() {
        return this.sym;
    }
}
