package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of literal integer/long values.
 * @author Carsten Otto, Marc Brockschmidt
 */
public final class LiteralInt extends AbstractInt implements Comparable<LiteralInt> {

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
     * The literal integer value.
     */
    private final BigInteger literal;

    /**
     * A constructor for a constant integer value.
     * @param constant the constant
     */
    LiteralInt(final BigInteger constant) {
        assert (constant != null);
        this.literal = constant;
    }

    /**
     * Convenience method for creating a literal.
     * @param bigInt the value of the literal
     * @return the literal
     */
    public static LiteralInt createLiteralInt(final BigInteger bigInt) {
        if (bigInt.equals(AbstractInt.getZero().literal)) {
            return AbstractInt.getZero();
        }
        if (bigInt.equals(AbstractInt.getOne().literal)) {
            return AbstractInt.getOne();
        }
        return new LiteralInt(bigInt);
    }

    /**
     * Convenience method for creating a literal.
     * @param longValue the value of the literal
     * @return the literal
     */
    static LiteralInt createLiteralInt(final long longValue) {
        return LiteralInt.createLiteralInt(BigInteger.valueOf(longValue));
    }

    /** {@inheritDoc} */
    @Override
    public LiteralInt absolute(final IntegerType intType) {
        if (this.literal.signum() >= 0) {
            return this;
        }
        final LiteralInt res = LiteralInt.createLiteralInt(this.literal.negate());
        return res;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt add(final AbstractInt n, final IntegerType intType) {
        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;
            if (o.isZero()) {
                return this;
            }
            final LiteralInt res = LiteralInt.createLiteralInt(this.literal.add(o.literal));
            return res;
        }

        return n.add(this, intType);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt and(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        if (sameReference) {
            assert (n instanceof LiteralInt);
            return n;
        }

        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;
            return LiteralInt.createLiteralInt(this.getLiteral().and(o.getLiteral()));
        }

        return n.and(this, sameReference, intType);
    }

    /** {@inheritDoc} */
    @Override
    public int compareTo(final LiteralInt n) {
        // We can actually do something on literals:
        return this.literal.compareTo((n).literal);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Integer compareToApprox(final AbstractInt other) {
        if (other instanceof LiteralInt) {
            return this.compareTo((LiteralInt) other);
        }
        final Integer res = other.compareToApprox(this);
        if (res != null) {
            return Integer.valueOf(res.intValue() * -1);
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsInt(final AbstractInt other) {
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

    /** {@inheritDoc} */
    @Override
    public Triple<? extends AbstractInt, Boolean, Boolean> div(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        if (n instanceof LiteralInt) {
            // Easy case: The divisor is also a literal
            final LiteralInt o = (LiteralInt) n;
            if (n.isZero()) {
                // If we only have a division by zero, do a shortcut here:
                return new Triple<AbstractInt, Boolean, Boolean>(null, Boolean.TRUE, Boolean.FALSE);
            }
            final LiteralInt res = LiteralInt.createLiteralInt(this.literal.divide(o.literal));
            return new Triple<AbstractInt, Boolean, Boolean>(res, Boolean.FALSE, !this.equals(res.mul(n, intType)));
        }
        return super.div(n, sameReference, intType);
    }

    /**
     * {@inheritDoc}
     */
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
        final LiteralInt other = (LiteralInt) obj;
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

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractNumber#getLiteralValue()
     */
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

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getLower() {
        return IntervalBound.create(this.literal);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getLowerCounter() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getMaxUpper() {
        return this.getLower();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getMinLower() {
        return IntervalBound.create(this.literal);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractBoundedInt getThisAsAbstractBoundedInt() {
        return AbstractBoundedInt.create(this.literal);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IntervalBound getUpper() {
        return this.getLower();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getUpperCounter() {
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.literal == null) ? 0 : this.literal.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public LiteralInt intersect(final AbstractNumber otherInt) throws IntersectionFailException {
        if (!(otherInt instanceof AbstractInt)) {
            throw new IntersectionFailException("not an int: " + this.toString() + " " + otherInt);
        }
        if (((AbstractInt) otherInt).containsInt(this)) {
            return this;
        }
        throw new IntersectionFailException("literal not contained: " + this.toString() + " " + otherInt);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractInt#isBiggerOne()
     */
    @Override
    public boolean isBiggerOne() {
        return this.literal.compareTo(BigInteger.ONE) > 0;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractNumber#isIntLiteral()
     */
    @Override
    public boolean isIntLiteral() {
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public boolean isLiteral() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNegative() {
        return this.literal.signum() < 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNegOne() {
        return this.literal.equals(BigInteger.ONE.negate());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNonNegative() {
        return this.literal.signum() >= 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNonPositive() {
        return this.literal.signum() <= 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isOne() {
        return this.literal.equals(BigInteger.ONE);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPositive() {
        return this.literal.signum() > 0;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractInt#isSmallerMinusOne()
     */
    @Override
    public boolean isSmallerMinusOne() {
        return this.literal.compareTo(BigInteger.ONE.negate()) < 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isZero() {
        return this.literal.equals(BigInteger.ZERO);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt mul(final AbstractInt n, final IntegerType intType) {
        if (this.isZero()) {
            return this;
        }
        if (this.isOne()) {
            return n;
        }
        if (this.isNegOne()) {
            return n.negate(intType);
        }

        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;
            final LiteralInt res = LiteralInt.createLiteralInt(this.literal.multiply(o.literal));
            return res;
        }

        return n.mul(this, intType);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt negate(final IntegerType intType) {
        final LiteralInt res = LiteralInt.createLiteralInt(this.literal.negate());
        return res;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt or(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        if (sameReference) {
            assert (n instanceof LiteralInt);
            return n;
        }

        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;
            return LiteralInt.createLiteralInt(this.getLiteral().or(o.getLiteral()));
        }
        return n.or(this, sameReference, intType);
    }

    /** {@inheritDoc} */
    @Override
    public Pair<? extends AbstractInt, Boolean> rem(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        if (n instanceof LiteralInt) {
            //Easy case: The divisor is also a literal
            final LiteralInt o = (LiteralInt) n;
            if (o.isZero()) {
                //If we only have a division by zero, do a shortcut here:
                return new Pair<>(null, Boolean.TRUE);
            }

            return new Pair<AbstractInt, Boolean>(
                LiteralInt.createLiteralInt(this.literal.remainder(o.literal)),
                Boolean.FALSE);
        }
        return super.rem(n, sameReference, intType);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt removeZeroFromInteger() {
        assert (!this.literal.equals(BigInteger.ZERO)) : "Trying to remove zero from literal zero!";
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt shl(final AbstractInt n, final IntegerType intType) {
        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;

            int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = o.getLiteral().intValue() & 0x3f;
            } else {
                lowerBits = o.getLiteral().intValue() & 0x1f;
            }
            BigInteger newLiteral;
            newLiteral = this.literal.shiftLeft(lowerBits);
            final LiteralInt res = AbstractInt.create(newLiteral);

            //No Overflow. Ever.
            return res;
        }
        return AbstractInt.getUnknown(IntegerType.UNBOUND);
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt shr(final AbstractInt n, final IntegerType intType) {
        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;

            int lowerBits;
            final boolean isLong = intType.getBitSize() == 64;
            if (isLong) {
                lowerBits = o.getLiteral().intValue() & 0x3f;
            } else {
                lowerBits = o.getLiteral().intValue() & 0x1f;
            }

            BigInteger newLiteral;
            newLiteral = this.getLiteral().shiftRight(lowerBits);

            //No Overflow. Ever.
            return AbstractInt.create(newLiteral);
        }
        return AbstractInt.getUnknown(IntegerType.UNBOUND);
    }

    /**
     * @return this value as DPTerm (i.e., using QDP/IDPv1 terms)
     */
    public TRSTerm toDPTerm() {
        return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(this.literal), DomainFactory.INTEGERS);
    }

    /**
     * @return an SMTLIB value corresponding to this literal.
     */
    public SMTExpression<SInt> toSMTExp() {
        return Ints.constant(this.literal);
    }

    /**
     * @return an SMTLIB value corresponding to this literal.
     */
    public SMTLIBIntValue toSMTIntValue() {
        return SMTLIBIntConstant.create(this.literal);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.literal.toString();
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt union(final AbstractInt o) {
        if (this.equals(o)) {
            return this;
        }

        final IntervalBound min = o.getLower().min(this.getLower());
        final IntervalBound max = o.getUpper().max(this.getUpper());
        final IntervalBound minLow = o.getMinLower().min(this.getMinLower());
        final IntervalBound maxUp = o.getMaxUpper().max(this.getMaxUpper());

        final boolean containsZero = this.isZero() || o.containsLiteral(0);
        return AbstractInt.create(min, max, containsZero, minLow, maxUp, o.getLowerCounter(), o.getUpperCounter());
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt ushr(final AbstractInt n, final IntegerType intType) {
        if (n instanceof LiteralInt) {
            assert (IntegerType.JAVA_LONG.canRepresent(this)) : "Cannot handle USHR for numbers not representable as Java long!";

            // this does not make much sense with an infinite number of bits
            if (this.isPositive()) {
                return this.shr(n, intType);
            }

            return AbstractInt.create(
                    IntervalBound.ZERO,
                    IntegerType.UNBOUND.getUpper(),
                    true,
                    IntervalBound.ZERO,
                    intType.getUpper(),
                    n.getLowerCounter(),
                    n.getUpperCounter());

        }
        return AbstractInt.create(
            IntervalBound.ZERO,
            intType.getUpper(),
            true,
            IntervalBound.ZERO,
            intType.getUpper(),
            n.getLowerCounter(),
            n.getUpperCounter());
    }

    /** {@inheritDoc} */
    @Override
    public AbstractInt xor(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType)
    {
        if (sameReference) {
            return AbstractInt.getZero();
        }

        if (n instanceof LiteralInt) {
            final LiteralInt o = (LiteralInt) n;
            return LiteralInt.createLiteralInt(this.getLiteral().xor(o.getLiteral()));
        }

        return n.xor(this, sameReference, intType);
    }

    @Override
    public Collection<String> toSExpStrings(final AbstractVariableReference ref) {
        if (this.isLiteral()) {
            String res = "(" + IntegerRelationType.EQ.toString() + " " + ref.toString() + " " + this.literal + ")";
            return Collections.singleton(res);
        } else {
            return Collections.emptyList();
        }
    }
}
