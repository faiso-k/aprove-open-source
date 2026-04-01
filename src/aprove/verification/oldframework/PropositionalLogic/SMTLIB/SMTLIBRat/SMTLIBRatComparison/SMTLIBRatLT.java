package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a < b
 *
 * @author CKuknat
 */
public class SMTLIBRatLT extends SMTLIBRatCMP {

    private SMTLIBRatLT(SMTLIBRatValue a, SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatLT create(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatLT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatLT createFromExisting(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatLT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatLT(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " < " + this.getB().toString();
    }

}
