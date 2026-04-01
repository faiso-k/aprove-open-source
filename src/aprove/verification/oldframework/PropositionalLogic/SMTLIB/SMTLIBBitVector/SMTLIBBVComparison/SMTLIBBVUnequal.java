package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;

/**
 * a!=b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVUnequal extends SMTLIBBVCMP {

    private SMTLIBBVUnequal(SMTLIBBVValue a, SMTLIBBVValue b) {
        super(a, b);
    }

    public static SMTLIBBVUnequal create(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVUnequal(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBBVUnequal createFromExisting(SMTLIBBVValue a, SMTLIBBVValue b) {
        return new SMTLIBBVUnequal(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVUnequal(this);
    }

}
