package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector;

import java.math.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * An arbitrary bitvector value.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVConstant extends SMTLIBConstant<SMTLIBBVValue> implements SMTLIBBVValue {

    private final BigInteger value;
    private final int len;

    private SMTLIBBVConstant(final BigInteger value, final int len) {
        this.value = value;
        this.len = len;
    }

    public static SMTLIBBVConstant create(final BigInteger value, final int len) {
        return new SMTLIBBVConstant(value, len);
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseBVConstant(this);
    }

    public BigInteger getValue() {
        return this.value;
    }

    @Override
    public int getLen() {
        return this.len;
    }

}
