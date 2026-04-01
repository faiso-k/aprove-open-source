package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public abstract class Macro3<RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort>
    extends
        Symbol3<RV, A0, A1, A2> implements Macro<RV>
{

    public Macro3(RV rv, A0 a0, A1 a1, A2 a2) {
        super(rv, a0, a1, a2);
    }

    public abstract SMTExpression<RV> body(SMTExpression<A0> a0, SMTExpression<A1> a1, SMTExpression<A2> a2);
}
