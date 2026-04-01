package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * Multiply two bitvectors.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVMul extends SMTLIBBVBinaryFunc {

    private SMTLIBBVMul(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVMul create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVMul(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVMul createFromExisting(final SMTLIBBVValue opA, final SMTLIBBVValue opB) {
        return SMTLIBBVMul.create(opA, opB);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        visitor.caseBVMul(this);
        return null;
    }

}
