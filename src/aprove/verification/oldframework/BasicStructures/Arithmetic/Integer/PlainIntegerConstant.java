package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.math.*;

/**
 * Just a wrapper for a big integer.
 * @author cryingshadow
 * @version $Id$
 */
public class PlainIntegerConstant implements IntegerConstant {

    /**
     * The constant 1.
     */
    public static final PlainIntegerConstant ONE = new PlainIntegerConstant(BigInteger.ONE);

    /**
     * The constant 0.
     */
    public static final PlainIntegerConstant ZERO = new PlainIntegerConstant(BigInteger.ZERO);

    /**
     * The value;
     */
    private final BigInteger value;

    /**
     * @param v The value.
     */
    public PlainIntegerConstant(BigInteger v) {
        this.value = v;
    }

    @Override
    public boolean equals(Object o) {
        return IntegerConstant.equals(this, o);
    }

    @Override
    public BigInteger getIntegerValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        return IntegerConstant.hashCode(this);
    }

    @Override
    public FunctionalIntegerExpression negate() {
        return new PlainIntegerConstant(this.getIntegerValue().negate());
    }

    @Override
    public String toString() {
        return this.toPrettyString();
    }

}
