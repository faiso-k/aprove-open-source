package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt;

import java.math.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * An arbitrary int value
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntConstant extends SMTLIBConstant<SMTLIBIntValue> implements SMTLIBIntValue {

    private final BigInteger value;

    private SMTLIBIntConstant(final BigInteger value) {
        this.value = value;
    }

    public static SMTLIBIntConstant create(final BigInteger value) {
        return new SMTLIBIntConstant(value);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseIntConstant(this);
    }

    public BigInteger getValue() {
        return this.value;
    }

    @Override
    public String toString() {
        return this.value.toString();
    }

}
