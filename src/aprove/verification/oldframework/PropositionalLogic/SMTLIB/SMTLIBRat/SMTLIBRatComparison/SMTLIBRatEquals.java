package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a=b
 *
 * @author CKuknat
 */
public class SMTLIBRatEquals extends SMTLIBRatCMP {

    private SMTLIBRatEquals(SMTLIBRatValue a, SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatEquals create(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatEquals(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatEquals createFromExisting(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatEquals(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatEquals(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " = " + this.getB().toString();
    }

}
