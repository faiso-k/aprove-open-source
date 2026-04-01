package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Substract two bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVSub extends SMTLIBBVBinaryFunc {

    private SMTLIBBVSub(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVSub create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVSub(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVSub createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVSub.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVSub(this);
        return null;
    }

}
