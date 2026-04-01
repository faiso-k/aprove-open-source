package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a <= b
 *
 * @author CKuknat
 */
public class SMTLIBRatLE extends SMTLIBRatCMP {

    private SMTLIBRatLE(SMTLIBRatValue a, SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatLE create(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatLE(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatLE createFromExisting(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatLE(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatLE(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " <= " + this.getB().toString();
    }

}
