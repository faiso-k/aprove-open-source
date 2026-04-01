package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a<b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVLT extends SMTLIBBVCMP {

    private SMTLIBBVLT(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVLT create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVLT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVLT createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVLT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVLT(this);
    }

}
