package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Enumeration of possible relations between two integers.
 * @author Christian von Essen, cryingshadow
 * @version $Id$
 */
public enum IntegerRelationType implements HasName {


    /**
     * Equal to.
     */
    EQ("="),

    /**
     * Greater than or equal to.
     */
    GE(">="),

    /**
     * Greater than.
     */
    GT(">"),

    /**
     * Less than or equal to.
     */
    LE("<="),

    /**
     * Less than.
     */
    LT("<"),

    /**
     * Unequal to.
     */
    NE("!=");

    /**
     * A short string representation.
     */
    private String string;

    /**
     * @param stringParam a short string representation
     */
    IntegerRelationType(final String stringParam) {
        this.string = stringParam;
    }

    /**
     * @param strict Strict relation?
     * @param greater Greater or less than?
     * @return The corresponding integer relation type.
     */
    public static IntegerRelationType create(final boolean strict, final boolean greater) {
        return strict ?
            (greater ? IntegerRelationType.GT : IntegerRelationType.LT) :
                (greater ? IntegerRelationType.GE : IntegerRelationType.LE);
    }

    /**
     * @return the inverse of this relation. For the original relation R and
     * the inverse R': xRy <=> !(xR'y)
     */
    public IntegerRelationType invert() {
        // sadly this cannot be done using the constructor and a cache
        switch (this) {
        case LT:
            return GE;
        case LE:
            return GT;
        case GT:
            return LE;
        case GE:
            return LT;
        case EQ:
            return NE;
        case NE:
            return EQ;
        default:
            throw new IllegalStateException("Someone found a new way to relate integers...");
        }
    }

    /**
     * @return the mirror of this relation. For the original relation R and
     * the mirror R': xRy <=> yR'x
     */
    public IntegerRelationType mirror() {
        // sadly this cannot be done using the constructor and a cache
        switch (this) {
        case LT:
            return GT;
        case LE:
            return GE;
        case GT:
            return LT;
        case GE:
            return LE;
        case EQ:
            return EQ;
        case NE:
            return NE;
        default:
            throw new IllegalStateException("Someone found a new way to relate integers...");
        }
    }

    /**
     * @param rel Some other relation.
     * @return True if for all values x,y where x this y holds also x rel y holds. False otherwise.
     */
    public boolean subSumes(final IntegerRelationType rel) {
        return (this == GT && (rel == GE || rel == NE))
            || (this == LT && (rel == LE || rel == NE))
            || (this == EQ && (rel == GE || rel == LE))
            || this == rel;
    }

    /**
     * @param rel Some other relation
     * @return True if there are no values x and y such that both x this y
     *  and x rel y hold
     */
    public boolean contradicts(final IntegerRelationType rel) {
        return (this == EQ && (rel == NE || rel == LT || rel == GT))
            || (this == NE && rel == EQ)
            || (this == LE && rel == GT)
            || (this == LT && (rel == EQ || rel == GE || rel == GT))
            || (this == GE && rel == LT)
            || (this == GT && (rel == EQ || rel == LE || rel == LT));
    }

    /**
     * @param other Some other integer type
     * @return A relation ret such that for all x and y the following holds:
     *  (x this y && x other y) <==> (x ret y). Null if that relation is not
     *  representable with this enum
     */
    public IntegerRelationType intersect(final IntegerRelationType other) {
        /* This first test covers all cases in which the return value is
         * this or null */
        if (this.equals(other)) {
            return this;
        } else if (this.contradicts(other)) {
            return null;
        }

        // We now have to deal with the remaining cases by hand
        switch (this) {
        case LT:
            assert other.equals(LE) || other.equals(NE) : "This should have been handled earlier";
            return LT;
        case LE:
            if (other.equals(LT) || other.equals(NE)) {
                return LT;
            } else if (other.equals(EQ) || other.equals(GE)) {
                return EQ;
            }
            assert false : "This should have been handled earlier";
            return null;
        case EQ:
            assert other.equals(LE) || other.equals(GE) : "This should have been handled earlier";
            return EQ;
        case NE:
            if (other.equals(LT) || other.equals(LE)) {
                return LT;
            } else if (other.equals(GE) || other.equals(GT)) {
                return GT;
            }
            assert false : "This should have been handled earlier";
            return null;
        case GE:
            if (other.equals(LE) || other.equals(EQ)) {
                return EQ;
            } else if (other.equals(NE) || other.equals(GT)) {
                return GT;
            }
            assert false : "This should have been handled earlier";
            return null;
        case GT:
            assert other.equals(NE) || other.equals(GE) : "This should have been handled earlier";
            return GT;
        default:
            assert false : "Someone found a new way to relate integers";
            return null;
        }
    }

    /**
     * @param other Some other integer type
     * @return A relation ret such that for all x and y the following holds:
     *  (x this y || x other y) <==> (x ret y). Null if that relation is not
     *  representable with this enum
     */
    public IntegerRelationType merge(final IntegerRelationType other) {
        /* This first test covers a lot of cases, but not all.
         * Example: LT.merge(GT) = NE, but this is not handled by this */
        if (this.equals(other)) {
            return this;
        } else if (other.subSumes(this)) {
            return this;
        } else if (this.subSumes(other)) {
            return other;
        }

        // Now we have to cover the remaining cases manually
        switch (this) {
        case LT:
            switch (other) {
            case EQ:
                return LE;
            case GE:
                return null;
            case GT:
                return NE;
            default:
                assert false : "This should have been handled earlier";
                return null;
            }
        case LE:
            assert other.equals(NE) || other.equals(GE) || other.equals(GT) : "This should have been handled earlier";
            return null;
        case EQ:
            switch (other) {
            case LT:
                return LE;
            case NE:
                return null;
            case GT:
                return GE;
            default:
                assert false : "This should have been handled earlier";
                return null;
            }
        case NE:
            assert other.equals(LE) || other.equals(EQ) || other.equals(GE) : "This should have been handled earlier";
            return null;
        case GE:
            assert other.equals(LT) || other.equals(LE) || other.equals(NE) : "This should have been handled earlier";
            return null;
        case GT:
            switch (other) {
            case LT:
                return NE;
            case LE:
                return null;
            case EQ:
                return GE;
            default:
                assert false : "This should have been handled earlier";
                return null;
            }
        default:
            assert false : "Someone found a new way to relate integers";
            return null;
        }

    }

    /**
     * @return If this is a directed inequality, return two boolean flags describing the same relation type 
     *         (strict, gerater). Null otherwise.
     */
    public Pair<Boolean, Boolean> toFlags() {
        switch (this) {
        case LE:
            return new Pair<Boolean, Boolean>(false, false);
        case LT:
            return new Pair<Boolean, Boolean>(true, false);
        case GE:
            return new Pair<Boolean, Boolean>(false, true);
        case GT:
            return new Pair<Boolean, Boolean>(true, true);
        default:
            return null;
        }
    }

    /**
     * @param leftValue some value for the left side
     * @param rightValue some value for the right side
     * @return <code>leftValue</code> REL <code>rightValue</code> as SMT atom
     */
    public SMTLIBTheoryAtom toSMTAtom(final SMTLIBIntValue leftValue, final SMTLIBIntValue rightValue) {
        switch (this) {
        case EQ:
            if (leftValue instanceof SMTLIBIntConstant && rightValue instanceof SMTLIBIntConstant) {
                return SMTLIBBoolTrue.create();
            } else {
                return SMTLIBIntEquals.create(leftValue, rightValue);
            }
        case NE:
            return SMTLIBIntUnequal.create(leftValue, rightValue);
        case LT:
            return SMTLIBIntLT.create(leftValue, rightValue);
        case LE:
            return SMTLIBIntLE.create(leftValue, rightValue);
        case GT:
            return SMTLIBIntGT.create(leftValue, rightValue);
        case GE:
            return SMTLIBIntGE.create(leftValue, rightValue);
        default:
            assert (false) : "Unknown relation type";
            return null;
        }
    }

    /**
     * @return If this is a directed inequality, return the strict version of it. Null otherwise.
     */
    public IntegerRelationType toStrict() {
        switch (this) {
        case LT:
        case LE:
            return IntegerRelationType.LT;
        case GT:
        case GE:
            return IntegerRelationType.GT;
        default:
            return null;
        }
    }

    public boolean isStrict() {
        switch (this) {
            case LT:
            case GT: return true;
            default: return false;
        }
    }

    public IntegerRelationType toNonStrict() {
        switch (this) {
            case LT:
            case LE:
                return IntegerRelationType.LE;
            case GT:
            case GE:
                return IntegerRelationType.GE;
            default:
                return null;
            }
    }

    /**
     * @return a short string representation
     */
    @Override
    public String toString() {
        return this.string;
    }

    public ChainableSymbol<? extends Sort> toChainableSymbol() throws NotChainableException {
        switch(this) {
            case EQ: return ChainableSymbol.Equivalent;
            case GT: return ChainableSymbol.IntsGreater;
            case GE: return ChainableSymbol.IntsGreaterEqual;
            case LT: return ChainableSymbol.IntsLess;
            case LE: return ChainableSymbol.IntsLessEqual;
            case NE: throw new NotChainableException();
            default:
                assert false;
                return null;
        }
    }

    /**
     * @return all relations that hold when this holds, including this
     */
    public List<IntegerRelationType> getWeakerRelationTypes() {
        switch (this) {
            case EQ: return Arrays.asList(new IntegerRelationType[]{LE, GE});
            case GT: return Arrays.asList(new IntegerRelationType[]{GE, NE});
            case LT: return Arrays.asList(new IntegerRelationType[]{LE, NE});
            case GE: return Collections.emptyList();
            case LE: return Collections.emptyList();
            case NE: return Collections.emptyList();
            default:
                assert false;
                return null;
        }
    }

    @Override
    public String getName() {
        return this.string;
    }

    @SuppressWarnings("serial")
    public static class NotChainableException extends Exception{}

}
