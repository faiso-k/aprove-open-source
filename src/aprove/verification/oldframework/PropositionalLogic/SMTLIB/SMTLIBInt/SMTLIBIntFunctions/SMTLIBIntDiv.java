package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;

/**
 * Representation of a / b
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBIntDiv extends SMTLIBIntArithFunc {

    private SMTLIBIntDiv(final List<SMTLIBIntValue> values) {
        super (values);
    }

    public static SMTLIBIntDiv create(final SMTLIBIntValue opA, final SMTLIBIntValue opB) {
        final List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
        operands.add(opA);
        operands.add(opB);
        return new SMTLIBIntDiv(operands);
    }

    public static SMTLIBIntDiv create(final List<SMTLIBIntValue> operands) {
        if (operands.size() != 2) {
            throw new UnsupportedOperationException("Can't do a div b div c.");
        }
        return new SMTLIBIntDiv(operands);
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBIntDiv createFromExisting(final List<SMTLIBIntValue> vals) {
        return SMTLIBIntDiv.create(vals);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntDiv(this);
    }

    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder();
        s.append('(')
         .append(this.getValues().get(0))
         .append(" / ")
         .append(this.getValues().get(1))
         .append(')');

        return s.toString();
    }

}
