package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat;

import java.math.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * An arbitrary int value
 *
 * @author CKuknat
 */
public class SMTLIBRatConstant extends SMTLIBConstant<SMTLIBRatValue> implements SMTLIBRatValue {

    public static final SMTLIBRatValue ZERO = new SMTLIBRatConstant(BigInteger.ZERO);
    public static final SMTLIBRatValue ONE = new SMTLIBRatConstant(BigInteger.ONE);

    private final MbyN value;

    private SMTLIBRatConstant(final MbyN value) {
        this.value = value;
    }

    private SMTLIBRatConstant(final BigInteger value) {
        this.value = MbyN.create(value);
    }

    public static SMTLIBRatConstant create(final MbyN value) {
        return new SMTLIBRatConstant(value);
    }

    public static SMTLIBRatConstant create(final BigInteger value) {
        return new SMTLIBRatConstant(value);
    }

    public static SMTLIBRatConstant create(final BigInteger m, final BigInteger n) {
        return new SMTLIBRatConstant(MbyN.create(m, n));
    }

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseRatConstant(this);
    }

    public MbyN getValue() {
        return this.value;
    }

    @Override
    public String toString() {
        return this.value.toString();
    }

}
