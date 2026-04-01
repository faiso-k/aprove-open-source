package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * If-Then-Else for integer
 *
 * IF (some bool expression)
 * THEN (some int expression)
 * ELSE (some other int expression)
 *
 * @author CKuknat
 */
public class SMTLIBRatITE extends SMTLIBITE<SMTLIBRatValue> implements SMTLIBRatValue {
    private SMTLIBRatITE(final SMTLIBBoolValue condition, final SMTLIBRatValue thenValue, final SMTLIBRatValue elseValue) {
        super(condition, thenValue, elseValue);
    }

    public static SMTLIBRatITE create(final SMTLIBBoolValue condition, final SMTLIBRatValue thenValue, final SMTLIBRatValue elseValue) {
        return new SMTLIBRatITE(condition, thenValue, elseValue);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatITE createFromExisting(
            final SMTLIBBoolValue newCond,
            final SMTLIBRatValue newThenVal,
            final SMTLIBRatValue newElseVal) {
        return SMTLIBRatITE.create(newCond, newThenVal, newElseVal);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatITE(this);
    }

    @Override
    public SMTLIBRatValue getThenValue() {
        return this.thenValue;
    }

    @Override
    public SMTLIBRatValue getElseValue() {
        return this.elseValue;
    }

    @Override
    public String toString() {
        return "if (" + this.condition.toString() +") then ("
                + this.thenValue.toString() + ") else ("
                + this.elseValue.toString() + ")" ;
    }

}
