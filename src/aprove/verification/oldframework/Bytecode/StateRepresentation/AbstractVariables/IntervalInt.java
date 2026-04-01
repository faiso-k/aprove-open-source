package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;

/**
 * Representation of int/long values realized by storing an interval [x, y] of
 * represented values. [-inf, +inf] is used to represent all values.
 * <p>
 * The additional information !=0 can be used to represent ranges where 0 is
 * excluded. This is most likely used for [-infty,+infty]\{0}, but [-5, 5]\{0}
 * is also allowed. The IntervalInt [0, 5]\{0} is not valid.
 * @author Carsten Otto, Marc Brockschmidt
 */
public final class IntervalInt extends AbstractInt {

    /**
     * The string used to denote that the interval does not contain zero.
     */
    private static final String NO_ZERO = "\\{0}";

    /**
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @return true iff the interval given by low and up includes 0.
     */
    static boolean containsZero(final IntervalBound low, final IntervalBound up) {
        return (low.signum() <= 0) && (up.signum() >= 0);
    }

    /**
     * True iff 0 is represented (set to false to build a special case like
     * [-inf, +inf] \ {0}). This may only be set if the interval defined by the
     * lower and upper bounds includes zero. It may not be unset if the interval
     * contains zero, but exactly one of the bounds is zero (e.g. [0, 5]\{0}
     * must be implemented as [1,5] instead).
     */
    private final boolean containsZero;

    /**
     * The lower part of the interval.
     */
    private final IntervalBound lower;

    /**
     * This counter tells how often the interval was widened towards the lower
     * bound during abstraction.
     */
    private final int lowerCounter;

    /**
     * The maximal upper bound that was used for this interval.
     */
    private final IntervalBound maximalUpperBound;

    /**
     * The minimal lower bound that was used for this interval.
     */
    private final IntervalBound minimalLowerBound;

    /**
     * The upper part of the interval.
     */
    private final IntervalBound upper;

    /**
     * This counter tells how often the interval was widened towards the upper
     * bound during abstraction.
     */
    private final int upperCounter;

    /**
     * Create an unknown integer.
     * @param intType the expected integer type of the result, i.e., the bounds for the result.
     */
    IntervalInt(final IntegerType intType) {
        this.lower = intType.getLower();
        this.minimalLowerBound = intType.getLower();
        this.upper = intType.getUpper();
        this.maximalUpperBound = intType.getUpper();
        this.lowerCounter = 0;
        this.upperCounter = 0;
        this.containsZero = true;
    }

    /**
     * Create a new {@link IntervalInt} based on the two interval bounds.
     * @param low the lower bound of the interval
     * @param up the upper bound of the interval
     * @param containsZeroParam true iff the abstract integer also represents
     * zero
     * @param minLow the minimal lower bound used for this interval in its arithmetic history.
     *  If <code>low</code> is smaller, it is used instead.
     * @param maxUp the maximal upper bound used for this interval in its arithmetic history
     *  If <code>up</code> is bigger, it is used instead.
     * @param newLowerCounter how often the interval was widened towards the
     * lower bound during abstraction.
     * @param newUpperCounter how often the interval was widened towards the
     * upper bound during abstraction.
     */
    IntervalInt(
        final IntervalBound low,
        final IntervalBound up,
        final boolean containsZeroParam,
        final IntervalBound minLow,
        final IntervalBound maxUp,
        final int newLowerCounter,
        final int newUpperCounter
    ) {
        assert (low.compareTo(up) < 0);
        this.lower = low;
        this.upper = up;
        this.minimalLowerBound = low.min(minLow);
        this.maximalUpperBound = up.max(maxUp);
        this.lowerCounter = newLowerCounter;
        this.upperCounter = newUpperCounter;
        this.containsZero = containsZeroParam;
        if (Globals.useAssertions) {
            if (containsZeroParam) {
                assert (IntervalInt.containsZero(low, up));
            } else {
                // [0, x] and [0, y] are not okay
                assert (!low.isZero() && !up.isZero());
            }
        }
    }

    @Override
    public AbstractInt absolute(final IntegerType intType) {
        if (this.isNonNegative()) {
            return this;
        }
        IntervalBound low = IntervalBound.ZERO;
        if (!this.containsZero) {
            low = IntervalBound.ONE;
        }
        if (this.upper.isNegative()) {
            low = this.upper.abs();
        }
        final IntervalBound up = this.upper.max(this.lower.abs());
        final AbstractInt res =
            AbstractInt.create(
                low,
                up,
                this.containsZero,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter);

        return res;
    }

    @Override
    public AbstractInt add(final AbstractInt n, final IntegerType intType) {
        if (n.isZero()) {
            return this;
        }
        final IntervalBound newLow = this.lower.add(n.getLower());
        final IntervalBound newUp = this.upper.add(n.getUpper());
        return AbstractInt.combine(newLow, newUp, this, n, intType);
    }

    @Override
    public AbstractInt and(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType
    ) {
        if (sameReference) {
            return this;
        }
        IntervalBound lower, upper;
        /*
         * The first bit represents the sign. neg & neg stays neg, everything
         * else becomes pos.
         */
        if (this.isNegative() && n.isNegative()) {
            lower = IntegerType.UNBOUND.getLower();
            upper = IntervalBound.NEGONE;
        } else if (this.isNonNegative() && n.isNonNegative()) {
            // BearPerson said this.
            lower = IntervalBound.ZERO;
            upper = this.upper.min(n.getUpper());
        } else {
            lower = IntervalBound.ZERO;
            upper = IntegerType.UNBOUND.getUpper();
        }
        return AbstractInt.combine(lower, upper, this, n, intType);
    }

    @Override
    public Integer compareToApprox(final AbstractInt n) {
        if (this.upper.compareTo(n.getLower()) < 0) {
            // [a, b] < [c, d] for b < c
            return -1;
        }
        if (this.lower.compareTo(n.getUpper()) > 0) {
            // [a, b] > [c, d] for a < d
            return 1;
        }
        return null;
    }

    @Override
    public boolean containsInt(final AbstractInt other) {
        // Our lower bound should not be greater than the other's
        if ((this.lower.isFinite() || other.getLower().isFinite()) && this.lower.compareTo(other.getLower()) > 0) {
            return false;
        }
        // same for upper
        if ((this.upper.isFinite() || other.getUpper().isFinite()) && this.upper.compareTo(other.getUpper()) < 0) {
            return false;
        }
        // if we have the zero we don't care whether the other has
        if (this.containsZero) {
            return true;
        }
        return !other.containsLiteral(0);
    }

    @Override
    public boolean containsLiteral(final BigInteger i) {
        if (i.equals(BigInteger.ZERO)) {
            return this.containsZero;
        }
        if (this.lower.compareTo(i) <= 0) {
            return (this.upper.compareTo(i) >= 0);
        }
        return false;
    }

    /**
     * @param ref the reference pointing to <code>this</code>
     * @param label some label that is prepended to all variable names.
     * @return list of SMT atoms corresponding to the (finite) bounds of <code>this</code>.
     */
    public List<SMTLIBTheoryAtom> convertBoundsToSMTConstraints(
        final AbstractVariableReference ref,
        final String label
    ) {
        final List<SMTLIBTheoryAtom> constraints = new LinkedList<>();
        final IntervalBound low = this.getLower();
        final IntervalBound up = this.getUpper();
        if (low.isFinite()) {
            constraints.add(SMTLIBIntLE.create(SMTLIBIntConstant.create(low.getConstant()), ref.toSMTIntValue(label)));
        }
        if (up.isFinite()) {
            constraints.add(SMTLIBIntLE.create(ref.toSMTIntValue(label), SMTLIBIntConstant.create(up.getConstant())));
        }
        return constraints;
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
        final IntervalInt other = (IntervalInt) obj;
        if (this.containsZero != other.containsZero) {
            return false;
        }
        if (this.lower == null) {
            if (other.lower != null) {
                return false;
            }
        } else if (!this.lower.equals(other.lower)) {
            return false;
        }
        if (this.lowerCounter != other.lowerCounter) {
            return false;
        }
        if (this.upper == null) {
            if (other.upper != null) {
                return false;
            }
        } else if (!this.upper.equals(other.upper)) {
            return false;
        }
        if (this.upperCounter != other.upperCounter) {
            return false;
        }
        return true;
    }

    @Override
    public boolean equalsOnlyRepresentedValues(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IntervalInt other = (IntervalInt) obj;
        if (this.containsZero != other.containsZero) {
            return false;
        }
        if (this.lower == null) {
            if (other.lower != null) {
                return false;
            }
        } else if (!this.lower.equals(other.lower)) {
            return false;
        }
        if (this.upper == null) {
            if (other.upper != null) {
                return false;
            }
        } else if (!this.upper.equals(other.upper)) {
            return false;
        }
        return true;
    }

    @Override
    public BigInteger getLiteral() {
        assert (false);
        return null;
    }

    @Override
    public IntervalBound getLower() {
        return this.lower;
    }

    @Override
    public int getLowerCounter() {
        return this.lowerCounter;
    }

    @Override
    public IntervalBound getMaxUpper() {
        return this.maximalUpperBound;
    }

    @Override
    public IntervalBound getMinLower() {
        return this.minimalLowerBound;
    }

    @Override
    public AbstractBoundedInt getThisAsAbstractBoundedInt() {
        return
            AbstractBoundedInt.create(
                this.lower,
                this.upper,
                this.containsZero,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter
            );
    }

    @Override
    public IntervalBound getUpper() {
        return this.upper;
    }

    @Override
    public int getUpperCounter() {
        return this.upperCounter;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.containsZero ? 1231 : 1237);
        result = prime * result + ((this.lower == null) ? 0 : this.lower.hashCode());
        result = prime * result + this.lowerCounter;
        result = prime * result + ((this.upper == null) ? 0 : this.upper.hashCode());
        result = prime * result + this.upperCounter;
        return result;
    }

    @Override
    public AbstractInt intersect(AbstractNumber other) throws IntersectionFailException {
        if (!(other instanceof AbstractInt)) {
            throw new IntersectionFailException("not an int: " + this.toString() + " " + other);
        }
        if (other instanceof LiteralInt) {
            return ((LiteralInt)other).intersect(this);
        }
        final AbstractInt otherInt = (AbstractInt)other;
        IntervalBound newLower = this.lower.max(otherInt.getLower());
        IntervalBound newUpper = this.upper.min(otherInt.getUpper());
        final boolean contains0 = this.containsZero && otherInt.containsLiteral(0);
        if (!contains0) {
            if (newLower.isZero()) {
                newLower = IntervalBound.create(BigInteger.ONE);
            }
            if (newUpper.isZero()) {
                newUpper = IntervalBound.create(BigInteger.ONE.negate());
            }
        }
        if (newLower.compareTo(newUpper) > 0) {
            throw new IntersectionFailException("empty intersection: " + this + " and " + other);
        }
        return
            AbstractInt.create(
                newLower,
                newUpper,
                contains0,
                newLower,
                newUpper,
                Math.min(this.lowerCounter, otherInt.getLowerCounter()),
                Math.min(this.upperCounter, otherInt.getUpperCounter())
            );
    }

    @Override
    public boolean isBiggerOne() {
        return this.lower.compareTo(BigInteger.ONE) > 0;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    @Override
    public boolean isNegative() {
        return this.upper.isNegative();
    }

    @Override
    public boolean isNegOne() {
        return false;
    }

    @Override
    public boolean isNonNegative() {
        return this.lower.isNonNegative();
    }

    @Override
    public boolean isNonPositive() {
        return this.upper.isNonPositive();
    }

    @Override
    public boolean isOne() {
        return false;
    }

    @Override
    public boolean isPositive() {
        return this.lower.isPositive();
    }

    @Override
    public boolean isSmallerMinusOne() {
        return this.upper.compareTo(BigInteger.ONE.negate()) < 0;
    }

    @Override
    public boolean isZero() {
        return false;
    }

    @Override
    public AbstractInt mul(final AbstractInt n, final IntegerType intType) {
        if (n.isOne()) {
            return this;
        }
        if (n.isZero()) {
            return n;
        }
        if (n.isNegOne()) {
            return this.negate(intType);
        }
        //[a,b] * [c,d] = [min{ac,ad,bc,bd}, max{ac,ad,bc,bd}]
        final IntervalBound ac = this.lower.mul(n.getLower());
        final IntervalBound ad = this.lower.mul(n.getUpper());
        final IntervalBound bc = this.upper.mul(n.getLower());
        final IntervalBound bd = this.upper.mul(n.getUpper());
        final IntervalBound lowerBound = ac.min(ad).min(bc).min(bd);
        final IntervalBound upperBound = ac.max(ad).max(bc).max(bd);
        final boolean resWithZero = this.containsZero || n.containsLiteral(0);
        return AbstractInt.combine(lowerBound, upperBound, resWithZero, this, n, intType);
    }

    @Override
    public AbstractInt negate(final IntegerType intType) {
        final IntervalBound newLow = this.upper.negate();
        final IntervalBound newUp = this.lower.negate();
        final boolean newContainsZero = this.containsZero && IntervalInt.containsZero(newLow, newUp);
        final AbstractInt res =
            AbstractInt.create(
                newLow,
                newUp,
                newContainsZero,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter
            );
        res.copyComparisonsFrom(this);
        return res;
    }

    @Override
    public AbstractInt or(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType
    ) {
        if (sameReference) {
            return n;
        }
        IntervalBound lower, upper;
        /*
         * The first bit represents the sign. pos | pos stays pos, everything
         * else becomes neg.
         */
        if (this.isNonNegative() && n.isNonNegative()) {
            // BearPerson said this.
            lower = this.lower.max(n.getLower());
            upper = IntegerType.UNBOUND.getUpper();
        } else {
            lower = IntegerType.UNBOUND.getLower();
            upper = IntervalBound.NEGONE;
        }
        return AbstractInt.combine(lower, upper, this, n, intType);
    }

    @Override
    public AbstractInt removeZeroFromInteger() {
        if (!this.containsZero) {
            return this;
        }
        IntervalBound newLow = this.lower;
        if (this.lower.isZero()) {
            newLow = IntervalBound.ONE;
        }
        IntervalBound newUp = this.upper;
        if (this.upper.isZero()) {
            newUp = IntervalBound.NEGONE;
        }
        return
            AbstractInt.create(
                newLow,
                newUp,
                false,
                this.minimalLowerBound,
                this.maximalUpperBound,
                this.lowerCounter,
                this.upperCounter
            );
    }

    @Override
    public AbstractInt shl(final AbstractInt n, final IntegerType intType) {
        if (n.isLiteral()) {
            final BigInteger literalValue = n.getLiteral();
            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue.intValue() & 0x3f;
            } else {
                lowerBits = literalValue.intValue() & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
            IntervalBound newLow;
            if (this.getLower().isFinite()) {
                newLow = IntervalBound.create(this.getLower().getConstant().shiftLeft(lowerBits));
            } else {
                newLow = this.getLower();
            }
            IntervalBound newUp;
            if (this.getUpper().isFinite()) {
                newUp = IntervalBound.create(this.getUpper().getConstant().shiftLeft(lowerBits));
            } else {
                newUp = this.getUpper();
            }
            final AbstractInt res =
                AbstractInt.create(
                    newLow,
                    newUp,
                    this.minimalLowerBound,
                    this.maximalUpperBound,
                    this.lowerCounter,
                    this.upperCounter
                );
            return res;
        }
        return AbstractInt.getUnknown(IntegerType.UNBOUND);
    }

    @Override
    public AbstractInt shr(final AbstractInt n, final IntegerType intType) {
        if (n.isLiteral()) {
            final BigInteger literalValue = n.getLiteral();
            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue.intValue() & 0x3f;
            } else {
                lowerBits = literalValue.intValue() & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
        }
        return AbstractInt.getUnknown(IntegerType.UNBOUND);
    }

    @Override
    public Collection<String> toSExpStrings(final AbstractVariableReference ref) {
        final List<String> res = new LinkedList<>();
        if (this.lower.isFinite()) {
            LiteralInt lowerBound = new LiteralInt(this.lower.getConstant());
            JBCIntegerRelation rel = new JBCIntegerRelation(lowerBound, IntegerRelationType.LE, ref);
            res.add(rel.toSExpString());
        }
        if (this.upper.isFinite()) {
            LiteralInt upperBound = new LiteralInt(this.upper.getConstant());
            JBCIntegerRelation rel = new JBCIntegerRelation(upperBound, IntegerRelationType.GE, ref);
            res.add(rel.toSExpString());
        }
        return res;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (!this.lower.isFinite() && !this.upper.isFinite()) {
            sb.append(AbstractInt.UNKNOWN_SIGN);
        } else {
            sb.append(this.lower.isFinite() ? "[" : "(");
            sb.append(this.lower.toString());
            sb.append(",");
            sb.append(this.upper.toString());
            sb.append(this.upper.isFinite() ? "]" : ")");
        }
        if (
            !this.containsZero
            && !this.lower.isZero()
            && !this.upper.isZero()
            && IntervalInt.containsZero(this.lower, this.upper)
        ) {
            sb.append(IntervalInt.NO_ZERO);
        }
        final boolean showLower = this.lowerCounter > 0 && this.lower.isFinite();
        final boolean showUpper = this.upperCounter > 0 && this.getUpper().isFinite();
        if (showLower && showUpper) {
            sb.append("(");
            sb.append(this.lowerCounter);
            sb.append(",");
            sb.append(this.upperCounter);
            sb.append(")");
        } else if (showLower) {
            sb.append("(l");
            sb.append(this.lowerCounter);
            sb.append(")");
        } else if (showUpper) {
            sb.append("(u");
            sb.append(this.upperCounter);
            sb.append(")");
        }
        if (!this.getMinLower().equals(this.lower) || !this.getMaxUpper().equals(this.upper)) {
            sb.append("{");
            sb.append(this.getMinLower().toString());
            sb.append(",");
            sb.append(this.getMaxUpper().toString());
            sb.append("}");
        }
        return sb.toString();
    }

    @Override
    public AbstractInt union(final AbstractInt o) {
        final IntervalBound newLow = this.lower.min(o.getLower());
        final IntervalBound newUp = this.upper.max(o.getUpper());
        final boolean newContainsZero = this.containsZero || o.containsLiteral(0);
        final int newLowerCounter = Math.max(this.lowerCounter, o.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, o.getUpperCounter());
        return
            AbstractInt.create(
                newLow,
                newUp,
                newContainsZero,
                this.minimalLowerBound.min(o.getMinLower()),
                this.maximalUpperBound.max(o.getMaxUpper()),
                newLowerCounter,
                newUpperCounter
            );
    }

    @Override
    public AbstractInt ushr(final AbstractInt n, final IntegerType intType) {
        if (n.isLiteral()) {
            final int literalValue = n.getLiteral().intValue();
            final int lowerBits;
            if (intType.getBitSize() == 64) {
                lowerBits = literalValue & 0x3f;
            } else {
                lowerBits = literalValue & 0x1f;
            }
            if (lowerBits == 0) {
                return this;
            }
        }
        final int newLowerCounter = Math.max(this.lowerCounter, n.getLowerCounter());
        final int newUpperCounter = Math.max(this.upperCounter, n.getUpperCounter());
        return
            AbstractInt.create(
                IntervalBound.ZERO,
                IntegerType.UNBOUND.getUpper(),
                true,
                this.minimalLowerBound,
                this.maximalUpperBound,
                newLowerCounter,
                newUpperCounter
            );
    }

    /**
     * @return true iff the value was already widened in a merge
     */
    public boolean wasWidened() {
        return this.upperCounter > 0;
    }

    @Override
    public AbstractInt xor(
        final AbstractInt n,
        final boolean sameReference,
        final IntegerType intType
    ) {
        if (sameReference) {
            return AbstractInt.getZero();
        }
        IntervalBound lower, upper;
        if ((this.isNonNegative() && n.isNegative()) || (this.isNegative() && n.isNonNegative())) {
            // different sign bits -> 1 -> negative
            lower = IntegerType.UNBOUND.getLower();
            upper = IntervalBound.NEGONE;
        } else if ((this.isNegative() && n.isNegative()) || (this.isNonNegative() && n.isNonNegative())) {
            // same sign bits -> 0 -> nonnegative
            lower = IntervalBound.ZERO;
            upper = IntegerType.UNBOUND.getUpper();
        } else {
            return AbstractInt.getUnknown(IntegerType.UNBOUND);
        }
        return AbstractInt.combine(lower, upper, this, n, intType);
    }

}
