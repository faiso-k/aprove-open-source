package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a - b - c - d - ...
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntMinus extends SMTLIBIntArithFunc {

    private SMTLIBIntMinus(List<SMTLIBIntValue> values) {
        super (values);
    }

    public static SMTLIBIntMinus create(List<SMTLIBIntValue> values) {
        return new SMTLIBIntMinus(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntMinus createFromExisting(final List<SMTLIBIntValue> vals) {
        return SMTLIBIntMinus.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntMinus(this);
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append('(');
        for (SMTLIBIntValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" - ");
        }
        return s.substring(0, s.length()-3) + ')';
    }

}
