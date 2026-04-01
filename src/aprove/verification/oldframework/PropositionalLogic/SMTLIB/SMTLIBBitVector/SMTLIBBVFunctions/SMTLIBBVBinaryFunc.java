package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Binary functions on two bitvectors.
 * Attend that both values of these functions must have the same length.
 * This will NOT be checked here!
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBBVBinaryFunc extends SMTLIBBinaryFunc<SMTLIBBVValue> implements SMTLIBBVValue {
    protected SMTLIBBVBinaryFunc(final SMTLIBBVValue a, final SMTLIBBVValue b) {
        super(a, b);
    }

    @Override
    public int getLen() {
        // Length of a and b must be the same, this will NOT be checked here!
        return this.getA().getLen();
    }
}
