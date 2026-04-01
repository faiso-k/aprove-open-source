package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * a * b * c * d * ...
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntMult extends SMTLIBIntArithFunc implements MayRequireNonLinearArithmetic {

    private SMTLIBIntMult(List<SMTLIBIntValue> values) {
        super (values);
    }

    public static SMTLIBIntMult create(List<SMTLIBIntValue> values) {
        return new SMTLIBIntMult(values);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntMult createFromExisting(final List<SMTLIBIntValue> vals) {
        return SMTLIBIntMult.create(vals);
    }

    @Override
    public Object apply(SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntMult(this);
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append('(');
        for (SMTLIBIntValue v : this.getValues()) {
            s.append(v.toString());
            s.append(" * ");
        }
        return s.substring(0, s.length()-3) + ')';
    }

    /**
     * According to http://rise4fun.com/z3/tutorialcontent/guide, (* s t) is nonlinear if s and t are not numbers.
     * @return Whether at least two of the arguments are not numbers.
     */
    @Override
    public boolean requiresNonLinearArithmetic() {
        return this.numberOfConstantArgs() < this.getValues().size() - 1;
    }

    private int numberOfConstantArgs() {
        int res = 0;
        for (SMTLIBIntValue val: this.getValues()) {
            if (val instanceof SMTLIBIntConstant) {
                res++;
            }
        }
        return res;
    }

}
