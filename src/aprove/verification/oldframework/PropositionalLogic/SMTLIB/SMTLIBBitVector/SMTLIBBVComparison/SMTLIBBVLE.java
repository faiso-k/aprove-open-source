package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a<=b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVLE extends SMTLIBBVCMP {

    private SMTLIBBVLE(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVLE create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVLE(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVLE createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVLE(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVLE(this);
    }

}
