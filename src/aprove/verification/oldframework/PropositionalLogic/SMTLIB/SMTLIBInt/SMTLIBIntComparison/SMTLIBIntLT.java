package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a < b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntLT extends SMTLIBIntCMP {

    private SMTLIBIntLT(SMTLIBIntValue a, SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntLT create(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntLT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntLT createFromExisting(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntLT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntLT(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " < " + this.getB().toString();
    }

}
