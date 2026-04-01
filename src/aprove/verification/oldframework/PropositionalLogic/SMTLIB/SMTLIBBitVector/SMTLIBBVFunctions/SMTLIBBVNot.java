package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Bitwise negation on a bitvector
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVNot extends SMTLIBBVUnaryFunc {

    private SMTLIBBVNot(SMTLIBBVValue a) {
        super(a);
    }

    public static SMTLIBBVNot create(SMTLIBBVValue a) {
        return new SMTLIBBVNot(a);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVNot createFromExisting(final SMTLIBBVValue op) {
        return SMTLIBBVNot.create(op);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVNot(this);
        return null;
    }

}
