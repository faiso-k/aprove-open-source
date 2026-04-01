package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class LeftAssocCall<A0 extends Sort, A1 extends Sort> extends Call<A0> {

    private final ImmutableList<SMTExpression<A1>> args;
    private final SMTExpression<A0> first;
    private final LeftAssocSymbol<A0, A1> sym;

    public LeftAssocCall(LeftAssocSymbol<A0, A1> sym, SMTExpression<A0> first, ImmutableList<SMTExpression<A1>> args) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.first = first;
        this.args = args;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public ImmutableList<SMTExpression<A1>> getArgs() {
        return this.args;
    }

    public SMTExpression<A0> getFirst() {
        return this.first;
    }

    @Override
    public LeftAssocSymbol<A0, A1> getSym() {
        return this.sym;
    }
}
