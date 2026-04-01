package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a != b
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntUnequal extends SMTLIBIntCMP {

    private SMTLIBIntUnequal(SMTLIBIntValue a, SMTLIBIntValue b) {
        super(a, b);
    }

    public static SMTLIBIntUnequal create(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntUnequal(a, b);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntUnequal createFromExisting(SMTLIBIntValue a, SMTLIBIntValue b) {
        return new SMTLIBIntUnequal(a, b);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntUnequal(this);
    }

    @Override
    public String toString() {
        return this.getA().toString() + " != " + this.getB().toString();
    }

}
