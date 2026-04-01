package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a>b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVGT extends SMTLIBBVCMP {

    private SMTLIBBVGT(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVGT create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVGT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVGT createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVGT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVGT(this);
    }

}
