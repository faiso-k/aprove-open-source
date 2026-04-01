package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;

/**
 * a * b * c * d * ...
 *
 * WARNING: Multiplication is NOT DECIDABLE, so be careful with this!
 *
 * @author CKuknat
 */
public class SMTLIBRatMult extends SMTLIBRatArithFunc implements MayRequireNonLinearArithmetic {

    private SMTLIBRatMult(List<SMTLIBRatValue> values) {
        super (values);
    }

    public static SMTLIBRatMult create(List<SMTLIBRatValue> values) {
        return new SMTLIBRatMult(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBRatMult createFromExisting(final List<SMTLIBRatValue> vals) {
        return SMTLIBRatMult.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatMult(this);
    }

    @Override
    public String toString() {
        StringBuffer s = new StringBuffer();
        s.append("(");
        for (SMTLIBRatValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" * ");
        }
        return s.substring(0, s.length()-3) + ")";
    }

    /**
     * For SMT-RAT, non linear arithmetic is always a good choice.
     * @return true
     */
    @Override
    public boolean requiresNonLinearArithmetic() {
        return true;
    }

}
