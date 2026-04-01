package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat;

import java.math.*;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Variable of type int
 *
 * @author CKuknat
 */
public class SMTLIBRatVariable extends SMTLIBVariable<SMTLIBRatValue> implements SMTLIBRatValue {
    private MbyN result;

    private SMTLIBRatVariable(final String name) {
        super(name);
    }

    public static SMTLIBRatVariable create(final String name) {
        return new SMTLIBRatVariable(name);
    }

    /** {@inheritDoc} */
    @Override
    public String getTypeAsString(final SMTTypeTranslator types) {
        return types.rationals();
    }

    /** {@inheritDoc} */
    @Override
    public void setResult(final String result) {
		if (result == null) {
	        throw new IllegalArgumentException("result must not be null");
	   	}
	    final String s = result.trim();
	    final BigInteger numerator;
	    final BigInteger denominator;

	    try {
	        if (s.contains("/")) {
	            // Fraction form: "n/d" (allow BigInteger size, optional spaces)
	            final String[] nums = s.split("/", 2);
	            numerator   = new BigInteger(nums[0].trim());
	            denominator = (nums.length > 1) ? new BigInteger(nums[1].trim()) : BigInteger.ONE;
	        } else {
	            // Decimal / integer: parse exactly via BigDecimal
	            final java.math.BigDecimal bd = new java.math.BigDecimal(s);
	            final int scale = bd.scale(); // value = unscaled * 10^{-scale}
	            final BigInteger unscaled = bd.unscaledValue();

	            if (scale >= 0) {
	                numerator   = unscaled;
	                denominator = BigInteger.TEN.pow(scale);
	            } else {
	                // negative scale -> integer multiple of 10^(-scale)
	                numerator   = unscaled.multiply(BigInteger.TEN.pow(-scale));
	                denominator = BigInteger.ONE;
	            }
	        }

	        if (denominator.signum() == 0) {
	            throw new ArithmeticException("denominator must not be zero");
	        }

	        // Let MbyN.create handle normalization/reduction/signs.
	        this.result = MbyN.create(numerator, denominator);
	    } catch (NumberFormatException e) {
	        throw new IllegalArgumentException("Invalid numeric string: " + s, e);
	    }
    }

    public MbyN getResultAsMbyN() {
        return this.result;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.getName() + (this.getResultAsMbyN() != null ? "; " + this.getResultAsMbyN(): "");
    }
}
