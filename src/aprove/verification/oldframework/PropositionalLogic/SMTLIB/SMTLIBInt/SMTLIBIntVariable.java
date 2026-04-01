package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt;

import java.math.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Variable of type int
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBIntVariable extends SMTLIBVariable<SMTLIBIntValue> implements SMTLIBIntValue {
    private BigInteger result;

    private SMTLIBIntVariable(final String name) {
        super(name);
    }

    public static SMTLIBIntVariable create(final String name) {
        return new SMTLIBIntVariable(name);
    }

    @Override
    public String getTypeAsString(final SMTTypeTranslator types) {
        return types.integers();
    }

    @Override
    public void setResult(final String entry) {
        this.result = new BigInteger(entry);
    }

    public BigInteger getResultAsBigInteger() {
        return this.result;
    }

    @Override
    public String toString() {
        return this.getName() + (this.getResultAsBigInteger() != null ? "; " + this.getResultAsBigInteger() : "");
    }
}
