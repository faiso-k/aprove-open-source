package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a > b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntGT extends SMTLIBIntCMP {

    private SMTLIBIntGT(SMTLIBIntValue a, SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntGT create(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntGT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntGT createFromExisting(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntGT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntGT(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " > " + this.getB().toString();
    }

}
