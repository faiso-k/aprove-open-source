package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Bitwise AND on bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVAnd extends SMTLIBBVBinaryFunc {

    private SMTLIBBVAnd(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVAnd create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVAnd(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVAnd createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVAnd.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVAnd(this);
        return null;
    }

}
