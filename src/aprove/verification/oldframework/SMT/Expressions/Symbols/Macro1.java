package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public abstract class Macro1<RV extends Sort, A0 extends Sort> extends Symbol1<RV, A0> implements Macro<RV> {
    public Macro1(RV rv, A0 a0) {
        super(rv, a0);
    }

    public abstract SMTExpression<RV> body(SMTExpression<A0> a0);
}
