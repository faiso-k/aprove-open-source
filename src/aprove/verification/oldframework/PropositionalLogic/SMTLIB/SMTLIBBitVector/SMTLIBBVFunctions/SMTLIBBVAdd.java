package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Add two bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVAdd extends SMTLIBBVBinaryFunc {

    private SMTLIBBVAdd(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVAdd create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVAdd(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVAdd createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVAdd.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVAdd(this);
        return null;
    }
}
