package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Bitwise XOR on bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVXor extends SMTLIBBVBinaryFunc {

    private SMTLIBBVXor(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVXor create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVXor(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVXor createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVXor.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVXor(this);
        return null;
    }

}
