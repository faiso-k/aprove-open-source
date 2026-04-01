package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * If-Then-Else for integer
 *
 * IF (some bool expression)
 * THEN (some int expression)
 * ELSE (some other int expression)
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntITE extends SMTLIBITE<SMTLIBIntValue> implements SMTLIBIntValue {
    private SMTLIBIntITE(final SMTLIBBoolValue condition, final SMTLIBIntValue thenValue, final SMTLIBIntValue elseValue) {
        super(condition, thenValue, elseValue);
    }

    public static SMTLIBIntITE create(final SMTLIBBoolValue condition, final SMTLIBIntValue thenValue, final SMTLIBIntValue elseValue) {
        return new SMTLIBIntITE(condition, thenValue, elseValue);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntITE createFromExisting(
            final SMTLIBBoolValue newCond,
            final SMTLIBIntValue newThenVal,
            final SMTLIBIntValue newElseVal) {
        return SMTLIBIntITE.create(newCond, newThenVal, newElseVal);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntITE(this);
    }

    @Override
    public SMTLIBIntValue getThenValue() {
        return this.thenValue;
    }

    @Override
    public SMTLIBIntValue getElseValue() {
        return this.elseValue;
    }

    @Override
    public String toString() {
        return "if (" + this.condition.toString() +") then ("
                + this.thenValue.toString() + ") else ("
                + this.elseValue.toString() + ")" ;
    }
}
