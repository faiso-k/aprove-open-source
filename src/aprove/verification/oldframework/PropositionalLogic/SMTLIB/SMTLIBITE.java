package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;


/**
 * If-Then-Else
 *
 * IF (some bool expression)
 * THEN (some expression)
 * ELSE (some other expression)
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBITE<T extends SMTLIBValue> implements SMTLIBValue {
    protected final T thenValue;
    protected final T elseValue;
    protected final SMTLIBBoolValue condition;

    protected SMTLIBITE(final SMTLIBBoolValue condition, final T thenVal, final T elseVal) {
        this.condition = condition;
        this.thenValue = thenVal;
        this.elseValue = elseVal;
    }

    public SMTLIBBoolValue getCondition() {
        return this.condition;
    }

    /**
     * @param newCond the new condition
     * @param newThenVal the new then value
     * @param newElseVal the new else value
     * @return a new instance of the ITE this was called on, with the
     *  given arguments. Consequently, only the type of the ITE is kept,
     *  not the arguments.
     */
    public abstract SMTLIBITE<T> createFromExisting(SMTLIBBoolValue newCond, T newThenVal, T newElseVal);

    public abstract T getThenValue();

    public abstract T getElseValue();

    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTITE(this);
        this.condition.apply(visitor);
        this.thenValue.apply(visitor);
        this.elseValue.apply(visitor);
    }

}
