package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public abstract class Macro2<RV extends Sort, A0 extends Sort, A1 extends Sort> extends Symbol2<RV, A0, A1>
    implements
        Macro<RV>
{

    public Macro2(RV rv, A0 a0, A1 a1) {
        super(rv, a0, a1);
    }

    public abstract SMTExpression<RV> body(SMTExpression<A0> a0, SMTExpression<A1> a1);
}
