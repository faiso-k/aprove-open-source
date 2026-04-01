package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * If-Then-Else for integer
 *
 * IF (some bool expression)
 * THEN (some int expression)
 * ELSE (some other int expression)
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBoolITE extends SMTLIBITE<SMTLIBBoolValue> implements SMTLIBBoolValue {
    private SMTLIBBoolITE(final SMTLIBBoolValue condition, final SMTLIBBoolValue thenValue, final SMTLIBBoolValue elseValue) {
        super(condition, thenValue, elseValue);
    }

    public static SMTLIBBoolITE create(final SMTLIBBoolValue condition, final SMTLIBBoolValue thenValue, final SMTLIBBoolValue elseValue) {
        return new SMTLIBBoolITE(condition, thenValue, elseValue);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBoolITE createFromExisting(
            final SMTLIBBoolValue newCond,
            final SMTLIBBoolValue newThenVal,
            final SMTLIBBoolValue newElseVal) {
        return SMTLIBBoolITE.create(newCond, newThenVal, newElseVal);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseBoolITE(this);
    }

    @Override
    public SMTLIBBoolValue getThenValue() {
        return this.thenValue;
    }

    @Override
    public SMTLIBBoolValue getElseValue() {
        return this.elseValue;
    }

}
