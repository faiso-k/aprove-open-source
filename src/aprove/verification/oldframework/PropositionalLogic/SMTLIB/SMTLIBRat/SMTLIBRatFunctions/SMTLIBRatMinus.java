package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a - b - c - d - ...
 *
 * @author CKuknat
 */
public class SMTLIBRatMinus extends SMTLIBRatArithFunc {

    private SMTLIBRatMinus(List<SMTLIBRatValue> values) {
        super (values);
    }

    public static SMTLIBRatMinus create(List<SMTLIBRatValue> values) {
        return new SMTLIBRatMinus(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatMinus createFromExisting(final List<SMTLIBRatValue> vals) {
        return SMTLIBRatMinus.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatMinus(this);
    }

    @Override
    public String toString() {
        StringBuffer s = new StringBuffer();
        s.append("(");
        for (SMTLIBRatValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" - ");
        }
        return s.substring(0, s.length()-3) + ")";
    }

}
