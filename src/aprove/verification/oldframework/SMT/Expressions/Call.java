package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;


public abstract class Call<R extends Sort> extends SMTExpression<R> {

    protected Call(R t) {
        super(t);
    }

    /**
     * @return the leading function symbol
     */
    public abstract Symbol<?> getSym();

}
