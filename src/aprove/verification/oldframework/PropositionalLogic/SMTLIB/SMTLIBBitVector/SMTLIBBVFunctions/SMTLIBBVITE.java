package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;

/**
 * If-Then-Else for bitvectors
 *
 * IF (some bool expression)
 * THEN (some int expression)
 * ELSE (some other int expression)
 *
 * Attend that the two bitvector values MUST have same length!
 * This will NOT be checked here!
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVITE extends SMTLIBITE<SMTLIBBVValue> implements SMTLIBBVValue {

    private SMTLIBBVITE(final SMTLIBBoolValue condition, final SMTLIBBVValue thenValue, final SMTLIBBVValue elseValue) {
        super(condition, thenValue, elseValue);
    }

    public static SMTLIBBVITE create(final SMTLIBBoolValue condition, final SMTLIBBVValue thenValue, final SMTLIBBVValue elseValue) {
        return new SMTLIBBVITE(condition, thenValue, elseValue);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVITE createFromExisting(
            final SMTLIBBoolValue newCond,
            final SMTLIBBVValue newThenVal,
            final SMTLIBBVValue newElseVal) {
        return SMTLIBBVITE.create(newCond, newThenVal, newElseVal);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVITE(this);
    }

    @Override
    public SMTLIBBVValue getThenValue() {
        return this.thenValue;
    }

    @Override
    public SMTLIBBVValue getElseValue() {
        return this.elseValue;
    }

    @Override
    public int getLen() {
        // Only acceptable if both values have the same length.
        // This is NOT checked here!
        return (this.thenValue).getLen();
    }
}
