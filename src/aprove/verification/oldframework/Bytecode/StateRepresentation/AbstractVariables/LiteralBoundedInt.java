package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of literal integer/long values.
 * @author Carsten Otto, Marc Brockschmidt, Jera Hensel
 */
public final class LiteralBoundedInt
extends AbstractBoundedInt
implements Comparable<LiteralBoundedInt>, IntegerConstant {

    /**
     * {@link Integer#MAX_VALUE}
     */
    public static final BigInteger MAXINT = new BigInteger(Integer.toString(Integer.MAX_VALUE));

    /**
     * {@link Long#MAX_VALUE}
     */
    public static final BigInteger MAXLONG = new BigInteger(Long.toString(Long.MAX_VALUE));

    /**
     * {@link Integer#MIN_VALUE}
     */
    public static final BigInteger MININT = new BigInteger(Integer.toString(Integer.MIN_VALUE));

    /**
     * {@link Long#MIN_VALUE}
     */
    public static final BigInteger MINLONG = new BigInteger(Long.toString(Long.MIN_VALUE));

    /**
     * Convenience method for creating a literal.
     * @param bigInt the value of the literal
     * @return the literal
     */
    static LiteralBoundedInt createLiteralInt(final BigInteger bigInt) {
        if (bigInt.equals(AbstractBoundedInt.getZero().literal)) {
            return AbstractBoundedInt.getZero();
        }
        if (bigInt.equals(AbstractBoundedInt.getOne().literal)) {
            return AbstractBoundedInt.getOne();
        }
        return new LiteralBoundedInt(bigInt);
    }

    /**
     * Convenience method for creating a literal.
     * @param longValue the value of the literal
     * @return the literal
     */
    static LiteralBoundedInt createLiteralInt(final long longValue) {
        return LiteralBoundedInt.createLiteralInt(BigInteger.valueOf(longValue));
    }

    /**
     * The literal integer value.
     */
    private final BigInteger literal;

    /**
     * A constructor for a constant integer value.
     * @param constant the constant
     */
    LiteralBoundedInt(final BigInteger constant) {
        assert (constant != null);
        this.literal = constant;
    }

    @Override
    public LiteralBoundedInt absolute(final IntegerType intType) throws OverflowException {
        if (this.literal.signum() >= 0) {
            return this;
        }
        final LiteralBoundedInt res = LiteralBoundedInt.createLiteralInt(this.literal.negate());
        if (!intType.canRepresent(res)) {
            throw new OverflowException(intType, ArithmeticOperationType.NEG, res);
        }
        return res;
    }

    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> add(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow
    ) throws OverflowException {
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            if (o.isZero()) {
                return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this, null, null);
            }
            LiteralBoundedInt res = LiteralBoundedInt.createLiteralInt(this.literal.add(o.literal));
            if (!intType.canRepresent(res)) {
                if (handleOverflows) {
                    res = (LiteralBoundedInt) res.adjustToBounds(intType, posOverflow, negOverflow).x;
                } else {
                    throw new OverflowException(intType, ArithmeticOperationType.ADD, res);
                }
            }
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, null, null);
        }
        return n.add(this, intType, handleOverflows);
    }

    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> adjustToBounds(
        final IntegerType intType,
        final YNM posOverflow,
        final YNM negOverflow
    ) {
        if (intType.canRepresent(this)) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this, null, null);
        } else {
            BigInteger res = this.getLiteral();
            BigInteger size = BigInteger.valueOf(2).pow(intType.getBitSize());
            // If the literal is above the valid range, lower it until it is in.
            while (res.compareTo(intType.getUpper().getConstant()) > 0) {
                res = res.subtract(size);
            }
            // If the literal is above the valid range, raise it until it is in.
            while (res.compareTo(intType.getLower().getConstant()) < 0) {
                res = res.add(size);
            }
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(AbstractBoundedInt.create(res), null, null);
        }
    }

    @Override
    public AbstractBoundedInt and(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows
    ) {
        if (sameReference) {
            assert (n instanceof LiteralBoundedInt);
            return n;
        }
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            return LiteralBoundedInt.createLiteralInt(this.getLiteral().and(o.getLiteral()));
        }
        return n.and(this, sameReference, intType, ignoreOverflows);
    }

    @Override
    public int compareTo(final LiteralBoundedInt n) {
        // We can actually do something on literals:
        return this.literal.compareTo((n).literal);
    }

    @Override
    public Integer compareToApprox(final AbstractBoundedInt other) {
        if (other instanceof LiteralBoundedInt) {
            return this.compareTo((LiteralBoundedInt) other);
        }
        final Integer res = other.compareToApprox(this);
        if (res != null) {
            return Integer.valueOf(res.intValue() * -1);
        }
        return null;
    }

    @Override
    public boolean containsInt(final AbstractBoundedInt other) {
        if (!other.isLiteral()) {
            return false;
        }
        return this.getLiteral().equals(other.getLiteral());
    }

    /**
     * @param i Integer to be checked
     * @return true iff i is this literal
     */
    @Override
    public boolean containsLiteral(final BigInteger i) {
        return this.literal.equals(i);
    }

    @Override
    public Triple<? extends AbstractBoundedInt, Boolean, Boolean> div(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows
    ) throws OverflowException {
        if (n instanceof LiteralBoundedInt) {
            // Easy case: The divisor is also a literal
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            if (n.isZero()) {
                // If we only have a division by zero, do a shortcut here:
                return new Triple<AbstractBoundedInt, Boolean, Boolean>(null, Boolean.TRUE, Boolean.FALSE);
            }
            final LiteralBoundedInt res = LiteralBoundedInt.createLiteralInt(this.literal.divide(o.literal));
            if (!intType.canRepresent(res)) {
                throw new OverflowException(intType, ArithmeticOperationType.TIDIV, res);
            }
            return new Triple<AbstractBoundedInt, Boolean, Boolean>(
                res,
                Boolean.FALSE,
                !this.equals(res.mul(n, intType, handleOverflows))
            );
        }
        return super.div(n, sameReference, intType, handleOverflows);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final LiteralBoundedInt other = (LiteralBoundedInt) obj;
        if (this.literal == null) {
            if (other.literal != null) {
                return false;
            }
        } else if (!this.literal.equals(other.literal)) {
            return false;
        }
        return true;
    }

    @Override
    public boolean equalsOnlyRepresentedValues(final Object obj) {
        return this.equals(obj);
    }

    @Override
    public BigInteger getIntegerValue() {
        return this.literal;
    }

    @Override
    public BigInteger getIntLiteralValue() {
        return this.getLiteral();
    }

    /**
     * @return the literal
     */
    @Override
    public BigInteger getLiteral() {
        return this.literal;
    }

    /**
     * @return the literal (as long value)
     */
    public long getLongValue() {
        return this.literal.longValue();
    }

    @Override
    public IntervalBound getLower() {
        return IntervalBound.create(this.literal);
    }

    @Override
    public int getLowerCounter() {
        return 0;
    }

    @Override
    public IntervalBound getMaxUpper() {
        return this.getLower();
    }

    @Override
    public IntervalBound getMinLower() {
        return IntervalBound.create(this.literal);
    }

    @Override
    public AbstractInt getThisAsAbstractInt() {
        return AbstractInt.create(this.literal);
    }

    @Override
    public IntervalBound getUpper() {
        return this.getLower();
    }

    @Override
    public int getUpperCounter() {
        return 0;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.literal == null) ? 0 : this.literal.hashCode());
        return result;
    }

    @Override
    public AbstractNumber intersect(final AbstractNumber otherInt) throws IntersectionFailException {
        if (!(otherInt instanceof AbstractBoundedInt)) {
            throw new IntersectionFailException("not an int: " + this.toString() + " " + otherInt);
        }
        if (((AbstractBoundedInt) otherInt).containsInt(this)) {
            return this;
        }
        throw new IntersectionFailException("literal not contained: " + this.toString() + " " + otherInt);
    }

    @Override
    public boolean isBiggerOne() {
        return this.literal.compareTo(BigInteger.ONE) > 0;
    }

    @Override
    public boolean isIntLiteral() {
        return true;
    }

    @Override
    public boolean isLiteral() {
        return true;
    }

    @Override
    public boolean isNegative() {
        return this.literal.signum() < 0;
    }

    @Override
    public boolean isNegOne() {
        return this.literal.equals(BigInteger.ONE.negate());
    }

    @Override
    public boolean isNonNegative() {
        return this.literal.signum() >= 0;
    }

    @Override
    public boolean isNonPositive() {
        return this.literal.signum() <= 0;
    }

    @Override
    public boolean isOne() {
        return this.literal.equals(BigInteger.ONE);
    }

    @Override
    public boolean isPositive() {
        return this.literal.signum() > 0;
    }

    @Override
    public boolean isSmallerMinusOne() {
        return this.literal.compareTo(BigInteger.ONE.negate()) < 0;
    }

    @Override
    public boolean isZero() {
        return this.literal.equals(BigInteger.ZERO);
    }

    @Override
    public Triple<AbstractBoundedInt, BigInteger, BigInteger> mul(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean handleOverflows,
        final YNM posOverflow,
        final YNM negOverflow
    ) throws OverflowException {
        if (this.isZero()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(this, null, null);
        }
        if (this.isOne()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(n, null, null);
        }
        if (this.isNegOne()) {
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(n.negate(intType), null, null);
        }
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            LiteralBoundedInt res = LiteralBoundedInt.createLiteralInt(this.literal.multiply(o.literal));
            if (!intType.canRepresent(res)) {
                if (handleOverflows) {
                    res = (LiteralBoundedInt) res.adjustToBounds(intType, posOverflow, negOverflow).x;
                } else {
                    throw new OverflowException(intType, ArithmeticOperationType.MUL, res);
                }
            }
            return new Triple<AbstractBoundedInt, BigInteger, BigInteger>(res, null, null);
        }
        return n.mul(this, intType, handleOverflows, posOverflow, negOverflow);
    }

    @Override
    public LiteralBoundedInt negate() {
        try {
            return this.negate(IntegerType.UNBOUND);
        } catch (OverflowException e) {
            throw new IllegalStateException("Overflows should not occur on unbounded operations!");
        }
    }

    @Override
    public LiteralBoundedInt negate(final IntegerType intType) throws OverflowException {
        final LiteralBoundedInt res = LiteralBoundedInt.createLiteralInt(this.literal.negate());
        if (!intType.canRepresent(res)) {
            throw new OverflowException(intType, ArithmeticOperationType.NEG, res);
        }
        return res;
    }

    @Override
    public AbstractBoundedInt or(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows
    ) {
        if (sameReference) {
            assert (n instanceof LiteralBoundedInt);
            return n;
        }
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            return LiteralBoundedInt.createLiteralInt(this.getLiteral().or(o.getLiteral()));
        }
        return n.or(this, sameReference, intType, ignoreOverflows);
    }

    @Override
    public Pair<? extends AbstractBoundedInt, Boolean> rem(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean handleOverflows
    ) {
        if (n instanceof LiteralBoundedInt) {
            //Easy case: The divisor is also a literal
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            if (o.isZero()) {
                //If we only have a division by zero, do a shortcut here:
                return new Pair<>(null, Boolean.TRUE);
            }
            return
                new Pair<AbstractBoundedInt, Boolean>(
                    LiteralBoundedInt.createLiteralInt(this.literal.remainder(o.literal)),
                    Boolean.FALSE
                );
        }
        return super.rem(n, sameReference, intType, handleOverflows);
    }

    @Override
    public AbstractBoundedInt removeZeroFromInteger() {
        assert (!this.literal.equals(BigInteger.ZERO)) : "Trying to remove zero from literal zero!";
        return this;
    }

    @Override
    public AbstractBoundedInt shl(final AbstractBoundedInt n, final IntegerType intType, final boolean ignoreOverflows) {
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = o.getLiteral().intValue() & 0x3f;
            } else {
                lowerBits = o.getLiteral().intValue() & 0x1f;
            }
            BigInteger newLiteral;
            if (ignoreOverflows) {
                newLiteral = this.literal.shiftLeft(lowerBits);
            } else {
                if (intType.getBitSize() == 32) {
                    newLiteral = BigInteger.valueOf(this.literal.intValue() << lowerBits);
                } else {
                    newLiteral = BigInteger.valueOf(this.literal.longValue() << lowerBits);
                }
            }
            final LiteralBoundedInt res = AbstractBoundedInt.create(newLiteral);
            //No Overflow. Ever.
            return res;
        }
        if (ignoreOverflows) {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        } else {
            return AbstractBoundedInt.getUnknown(intType);
        }
    }

    @Override
    public AbstractBoundedInt shr(final AbstractBoundedInt n, final IntegerType intType, final boolean ignoreOverflows) {
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            int lowerBits;
            final boolean isLong = intType.getBitSize() == 64;
            if (isLong) {
                lowerBits = o.getLiteral().intValue() & 0x3f;
            } else {
                lowerBits = o.getLiteral().intValue() & 0x1f;
            }
            BigInteger newLiteral;
            if (ignoreOverflows) {
                newLiteral = this.getLiteral().shiftRight(lowerBits);
            } else if (!isLong) {
                newLiteral = BigInteger.valueOf(this.getLiteral().longValue() >> lowerBits);
            } else {
                newLiteral = BigInteger.valueOf(this.getLiteral().intValue() >> lowerBits);
            }
            //No Overflow. Ever.
            return AbstractBoundedInt.create(newLiteral);
        }
        if (ignoreOverflows) {
            return AbstractBoundedInt.getUnknown(IntegerType.UNBOUND);
        } else {
            return AbstractBoundedInt.getUnknown(intType);
        }
    }

    @Override
    public AbstractBoundedInt toByteValue() throws OverflowException {
        final BigInteger newVal = BigInteger.valueOf(this.literal.byteValue());
        final LiteralBoundedInt res = new LiteralBoundedInt(newVal);
        if (newVal.compareTo(this.getLiteral()) != 0) {
            throw new OverflowException(IntegerType.I8, null, res);
        }
        return res;
    }

    @Override
    public AbstractBoundedInt toCharValue() throws OverflowException {
        final BigInteger newVal = BigInteger.valueOf((char) this.literal.intValue());
        final LiteralBoundedInt res = new LiteralBoundedInt(newVal);
        if (newVal.compareTo(this.getLiteral()) != 0) {
            throw new OverflowException(IntegerType.UI8, null, res);
        }
        return res;
    }

    /**
     * @return this value as DPTerm (i.e., using QDP/IDPv1 terms)
     */
    public TRSTerm toDPTerm() {
        return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(this.literal), DomainFactory.INTEGERS);
    }

    @Override
    public AbstractBoundedInt toIntegerValue() throws OverflowException {
        final BigInteger newVal = BigInteger.valueOf(this.literal.intValue());
        final LiteralBoundedInt res = new LiteralBoundedInt(newVal);
        if (newVal.compareTo(this.getLiteral()) != 0) {
            throw new OverflowException(IntegerType.I32, null, res);
        }
        return res;
    }

    @Override
    public AbstractBoundedInt toShortValue() throws OverflowException {
        final BigInteger newVal = BigInteger.valueOf(this.literal.shortValue());
        final LiteralBoundedInt res = new LiteralBoundedInt(newVal);
        if (newVal.compareTo(this.getLiteral()) != 0) {
            throw new OverflowException(IntegerType.I16, null, res);
        }
        return res;
    }

    /**
     * @return an SMTLIB value corresponding to this literal.
     */
    @Override
    public SMTExpression<SInt> toSMTExp() {
        return Ints.constant(this.literal);
    }

    /**
     * @return an SMTLIB value corresponding to this literal.
     */
    public SMTLIBIntValue toSMTIntValue() {
        return SMTLIBIntConstant.create(this.literal);
    }

    @Override
    public String toString() {
        return this.literal.toString();
    }

    @Override
    public AbstractBoundedInt union(final AbstractBoundedInt o) {
        if (this.equals(o)) {
            return this;
        }
        final IntervalBound min = o.getLower().min(this.getLower());
        final IntervalBound max = o.getUpper().max(this.getUpper());
        final IntervalBound minLow = o.getMinLower().min(this.getMinLower());
        final IntervalBound maxUp = o.getMaxUpper().max(this.getMaxUpper());
        final boolean containsZero = this.isZero() || o.containsLiteral(0);
        return
            AbstractBoundedInt.create(min, max, containsZero, minLow, maxUp, o.getLowerCounter(), o.getUpperCounter());
    }

    @Override
    public AbstractBoundedInt ushr(
        final AbstractBoundedInt n,
        final IntegerType intType,
        final boolean ignoreOverflows
    ) {
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            assert (IntegerType.JAVA_LONG.canRepresent(this)) :
                "Cannot handle USHR for numbers not representable as Java long!";
            final int lowerBits;
            final boolean isLong = intType.getBitSize() == 64;
            if (isLong) {
                lowerBits = o.getLiteral().intValue() & 0x3f;
            } else {
                lowerBits = o.getLiteral().intValue() & 0x1f;
            }
            if (ignoreOverflows) {
                // this does not make much sense with an infinite number of bits
                if (this.isPositive()) {
                    return this.shr(n, intType, ignoreOverflows);
                }
                return
                    AbstractBoundedInt.create(
                        IntervalBound.ZERO,
                        IntegerType.UNBOUND.getUpper(),
                        true,
                        IntervalBound.ZERO,
                        intType.getUpper(),
                        n.getLowerCounter(),
                        n.getUpperCounter()
                    );
            }
            long newLiteral;
            if (isLong) {
                newLiteral = this.getLiteral().longValue() >>> lowerBits;
            } else {
                newLiteral = this.getLiteral().intValue() >>> lowerBits;
            }
            return AbstractBoundedInt.create(newLiteral);
        }
        return
            AbstractBoundedInt.create(
                IntervalBound.ZERO,
                intType.getUpper(),
                true,
                IntervalBound.ZERO,
                intType.getUpper(),
                n.getLowerCounter(),
                n.getUpperCounter()
            );
    }

    @Override
    public AbstractBoundedInt xor(
        final AbstractBoundedInt n,
        final boolean sameReference,
        final IntegerType intType,
        final boolean ignoreOverflows
    ) {
        if (sameReference) {
            return AbstractBoundedInt.getZero();
        }
        if (n instanceof LiteralBoundedInt) {
            final LiteralBoundedInt o = (LiteralBoundedInt) n;
            return LiteralBoundedInt.createLiteralInt(this.getLiteral().xor(o.getLiteral()));
        }
        return n.xor(this, sameReference, intType, ignoreOverflows);
    }

    @Override
    public boolean isNonZero() {
        return !this.literal.equals(BigInteger.ZERO);
    }

}
