package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * integer negation on a bitvector
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVNeg extends SMTLIBBVUnaryFunc {

    private SMTLIBBVNeg(SMTLIBBVValue a) {
        super(a);
    }

    public static SMTLIBBVNeg create(SMTLIBBVValue a) {
        return new SMTLIBBVNeg(a);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVNeg createFromExisting(final SMTLIBBVValue op) {
        return SMTLIBBVNeg.create(op);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVNeg(this);
        return null;
    }

}
