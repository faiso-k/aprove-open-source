package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Concatenation of two bitvectors.
 *
 * @author Andreas Kelle-Emden
 *
 */
public class SMTLIBBVConcat extends SMTLIBBVBinaryFunc {

    private SMTLIBBVConcat(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVConcat create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVConcat(a,b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVBinaryFunc createFromExisting(SMTLIBBVValue opA,
            SMTLIBBVValue opB) {
        return SMTLIBBVConcat.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVConcat(this);
        return null;
    }

    @Override
    public int getLen() {
        // |ab| = |a|+|b|
        return this.getA().getLen()+this.getB().getLen();
    }
}
