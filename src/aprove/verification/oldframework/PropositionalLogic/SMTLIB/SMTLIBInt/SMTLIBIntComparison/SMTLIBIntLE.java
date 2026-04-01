package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a <= b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntLE extends SMTLIBIntCMP {

    private SMTLIBIntLE(SMTLIBIntValue a, SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntLE create(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntLE(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntLE createFromExisting(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntLE(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntLE(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " <= " + this.getB().toString();
    }

}
