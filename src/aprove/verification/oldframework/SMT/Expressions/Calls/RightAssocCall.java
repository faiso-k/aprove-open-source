package aprove.verification.oldframework.SMT.Expressions.Calls;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class RightAssocCall<A0 extends Sort, A1 extends Sort> extends Call<A1> {

    private final ImmutableList<SMTExpression<A0>> args;
    private final SMTExpression<A1> last;
    private final RightAssocSymbol<A0, A1> sym;

    public RightAssocCall(RightAssocSymbol<A0, A1> sym, ImmutableList<SMTExpression<A0>> args, SMTExpression<A1> last) {
        super(sym.getReturnSort());
        this.sym = sym;
        this.args = args;
        this.last = last;
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public ImmutableList<SMTExpression<A0>> getArgs() {
        return this.args;
    }

    public SMTExpression<A1> getLast() {
        return this.last;
    }

    @Override
    public RightAssocSymbol<A0, A1> getSym() {
        return this.sym;
    }
}
