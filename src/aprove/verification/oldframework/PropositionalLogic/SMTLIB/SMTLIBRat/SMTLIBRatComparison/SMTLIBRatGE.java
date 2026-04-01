package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a >= b
 *
 * @author CKuknat
 */
public class SMTLIBRatGE extends SMTLIBRatCMP {

    private SMTLIBRatGE(final SMTLIBRatValue a, final SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatGE create(final SMTLIBRatValue a, final SMTLIBRatValue b) {
        return new SMTLIBRatGE(a, b);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatGE(this);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatGE createFromExisting(final SMTLIBRatValue a, final SMTLIBRatValue b) {
        return new SMTLIBRatGE(a, b);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " >= " + this.getB().toString();
    }

}
