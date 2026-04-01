package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class ChainableCall<A0 extends Sort> extends Call<SBool> {

    private final ImmutableList<SMTExpression<A0>> args;
    private final ChainableSymbol<A0> sym;

    public ChainableCall(ChainableSymbol<A0> sym, ImmutableList<SMTExpression<A0>> args) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.args = args;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public ImmutableList<SMTExpression<A0>> getArgs() {
        return this.args;
    }

    @Override
    public ChainableSymbol<A0> getSym() {
        return this.sym;
    }
}
