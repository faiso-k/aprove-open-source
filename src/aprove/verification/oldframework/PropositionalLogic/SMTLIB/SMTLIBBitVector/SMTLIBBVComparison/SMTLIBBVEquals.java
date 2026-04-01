package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a=b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVEquals extends SMTLIBBVCMP {

    private SMTLIBBVEquals(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVEquals create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVEquals(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVEquals createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVEquals(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVEquals(this);
    }

}
