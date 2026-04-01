package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a != b
 *
 * @author CKuknat
 */
public class SMTLIBRatUnequal extends SMTLIBRatCMP {

    private SMTLIBRatUnequal(SMTLIBRatValue a, SMTLIBRatValue b) {
        super(a, b);
    }

    public static SMTLIBRatUnequal create(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatUnequal(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatUnequal createFromExisting(SMTLIBRatValue a, SMTLIBRatValue b) {
        return new SMTLIBRatUnequal(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatUnequal(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " != " + this.getB().toString();
    }

}
