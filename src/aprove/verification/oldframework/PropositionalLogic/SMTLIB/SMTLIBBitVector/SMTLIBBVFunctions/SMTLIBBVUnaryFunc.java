package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Base type for unary functions on bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBBVUnaryFunc extends SMTLIBUnaryFunc<SMTLIBBVValue> implements SMTLIBBVValue {
    protected SMTLIBBVUnaryFunc(final SMTLIBBVValue a) {
        super(a);
    }

    @Override
    public int getLen() {
        return this.getA().getLen();
    }
}
