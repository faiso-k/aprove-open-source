package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Bitwise OR on bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVOr extends SMTLIBBVBinaryFunc {

    private SMTLIBBVOr(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVOr create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVOr(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVOr createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVOr.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVOr(this);
        return null;
    }

}
