package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a + b + c + d + ...
 *
 * @author CKuknat
 */
public class SMTLIBRatPlus extends SMTLIBRatArithFunc {

    private SMTLIBRatPlus(List<SMTLIBRatValue> values) {
        super (values);
    }

    public static SMTLIBRatPlus create(List<SMTLIBRatValue> values) {
        return new SMTLIBRatPlus(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatPlus createFromExisting(final List<SMTLIBRatValue> vals) {
        return SMTLIBRatPlus.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatPlus(this);
    }

    @Override
    public String toString() {
        StringBuffer s = new StringBuffer();
        s.append("(");
        for (SMTLIBRatValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" + ");
        }
        return s.substring(0, s.length()-3) + ")";
    }

}
