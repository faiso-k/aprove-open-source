package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a >= b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntGE extends SMTLIBIntCMP {

    private SMTLIBIntGE(SMTLIBIntValue a, SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntGE create(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntGE(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntGE createFromExisting(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntGE(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntGE(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " >= " + this.getB().toString();
    }

}
