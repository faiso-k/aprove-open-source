package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a + b + c + d + ...
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntPlus extends SMTLIBIntArithFunc {

    private SMTLIBIntPlus(List<SMTLIBIntValue> values) {
        super (values);
    }

    public static SMTLIBIntPlus create(List<SMTLIBIntValue> values) {
        return new SMTLIBIntPlus(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntPlus createFromExisting(final List<SMTLIBIntValue> vals) {
        return SMTLIBIntPlus.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntPlus(this);
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append('(');
        for (SMTLIBIntValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" + ");
        }
        return s.substring(0, s.length()-3) + ')';
    }

}
