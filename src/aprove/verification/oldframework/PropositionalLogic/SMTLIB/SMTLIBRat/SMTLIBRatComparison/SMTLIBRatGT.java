package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a > b
 *
 * @author CKuknat
 */
public class SMTLIBRatGT extends SMTLIBRatCMP {

    private SMTLIBRatGT(SMTLIBRatValue a, SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatGT create(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatGT(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatGT createFromExisting(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatGT(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatGT(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " > " + this.getB().toString();
    }

}
