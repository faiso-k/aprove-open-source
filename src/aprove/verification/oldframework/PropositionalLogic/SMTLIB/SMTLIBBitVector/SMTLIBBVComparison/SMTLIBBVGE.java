package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a>=b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVGE extends SMTLIBBVCMP {

    private SMTLIBBVGE(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVGE create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVGE(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVGE createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVGE(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVGE(this);
    }

}
