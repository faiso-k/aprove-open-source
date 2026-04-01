package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a=b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntEquals extends SMTLIBIntCMP {

    private SMTLIBIntEquals(final SMTLIBIntValue a, final SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntEquals create(final SMTLIBIntValue a, final SMTLIBIntValue b) {
        if (a == null) {
            throw new RuntimeException("foo");
        }
        return new SMTLIBIntEquals(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntEquals createFromExisting(final SMTLIBIntValue a, final SMTLIBIntValue b) {
        return new SMTLIBIntEquals(a, b);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntEquals(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " = " + this.getB().toString();
    }

}
